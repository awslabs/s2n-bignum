"""Compare PR proof timings with saved timings for the tested base commit.

Timing artifacts are named after the git tree they measured, so any run
that tested the base commit's files can serve as the baseline.

The proof-timing-report CI job runs `python3 tools/proof_timing/report.py`.
It writes per-proof timings to one PR comment, updated in place on reruns,
and to the job summary. Regressions are flagged when a compatible baseline
is available. The baseline workflow runs it with `--missing` to decide
which architectures still need a proof run.
"""

import argparse
import json
import math
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from urllib.parse import urlencode

ARCHES = ('arm', 'x86')
BASELINE_WORKFLOW = 'proof-timing-baseline.yml'
# Only artifacts uploaded by these workflows count as timings.
TIMING_WORKFLOWS = ('.github/workflows/ci.yml', f'.github/workflows/{BASELINE_WORKFLOW}')
# Download at most this many artifacts per lookup, newest first.
CANDIDATES = 5
PROFILE_FIELDS = {'host', 'cpu', 'available_cpus', 'image', 'os', 'hol_light',
                  'opam_packages', 'native_tools', 'build_jobs', 'proof_jobs'}
TARGET = re.compile(r'[A-Za-z0-9_/-]+\.correct')
# Allowed rounding difference between `elapsed` and `end - start`, as in
# tools/proof_timing/collect.py.
ROUNDING = 1e-3

# The report comment starts with this marker so reruns can find and edit it.
COMMENT_TAG = '<!-- proof-timing-report -->'
# GitHub rejects comments longer than 65536 characters.
COMMENT_LIMIT = 65000
OK, WARN, FAIL = '✅', '⚠️', '❌'


class Unavailable(Exception):
    """A measurement or a piece of workflow metadata is unavailable."""


class NotFound(Unavailable):
    """GitHub answered 404, e.g. for a workflow that has never run."""


def git(*args):
    return subprocess.check_output(['git', *args], text=True).strip()


def artifact_name(arch, tree):
    # Artifacts are found repository-wide by this name. The timing of a PR's
    # merge commit therefore also serves main once the same files land there.
    return f'proof-timing-{arch}-{tree}'


class Actions:
    def __init__(self, repo):
        self.repo = repo
        self.runs = {}

    def gh(self, *args):
        result = subprocess.run(['gh', *args], capture_output=True, text=True)
        if result.returncode:
            if 'HTTP 404' in result.stderr:
                raise NotFound('not found')
            # Keep the report concise and the full CLI diagnostic in the job log.
            print(result.stderr.strip(), file=sys.stderr)
            raise Unavailable('GitHub lookup failed (see report job log)')
        return result.stdout

    def list(self, path, key, **filters):
        query = urlencode(dict(per_page=100, **filters))
        pages = self.gh('api', '--paginate', '--slurp', f'repos/{self.repo}/actions/{path}?{query}')
        return [entry for page in json.loads(pages) for entry in page[key]]

    def run(self, run_id):
        if run_id not in self.runs:
            self.runs[run_id] = json.loads(self.gh('api', f'repos/{self.repo}/actions/runs/{run_id}'))
        return self.runs[run_id]

    def timings(self, arch, tree, run_id=None):
        """Return valid timings of `tree` on `arch`, newest first, and any problems.

        With `run_id`, only that run's artifact is considered.
        """
        artifacts = [a for a in self.list('artifacts', 'artifacts', name=artifact_name(arch, tree))
                     if not a['expired'] and run_id in (None, a['workflow_run']['id'])]
        artifacts.sort(key=lambda a: a['created_at'], reverse=True)
        found, problems = [], []
        for artifact in artifacts[:CANDIDATES]:
            source = artifact['workflow_run']['id']
            try:
                if self.run(source)['path'].split('@')[0] not in TIMING_WORKFLOWS:
                    continue
                with tempfile.TemporaryDirectory() as directory:
                    self.gh('run', 'download', str(source), '--repo', self.repo,
                            '--name', artifact['name'], '--dir', directory)
                    data = json.loads((Path(directory) / 'timing.json').read_text())
                validate(data, arch, tree, source)
            except Unavailable as error:
                problems.append(str(error))
            except (ValueError, KeyError, TypeError, AttributeError, OverflowError, OSError):
                problems.append(f'invalid timing artifact in run {source}')
            else:
                found.append(data)
        return found, problems


def validate(data, arch, tree, run_id):
    identity = (data['version'], data['arch'], data['tree'], data['run_id'])
    if identity != (1, arch, tree, run_id):
        raise ValueError('artifact identity mismatch')
    if (not isinstance(data['sha'], str) or not isinstance(data['attempt'], int)
            or not isinstance(data['profile'], dict) or not isinstance(data['proof_success'], bool)):
        raise ValueError('invalid run metadata')
    for phase, seconds in data['phases'].items():
        if phase not in ('build', 'proof') or not math.isfinite(seconds) or seconds < 0:
            raise ValueError('invalid phase duration')
    names = set()
    for row in data['targets']:
        name = row['target']
        if not TARGET.fullmatch(name) or name in names or name.startswith('/'):
            raise ValueError('unexpected or duplicate target')
        names.add(name)
        if row['kind'] not in ('spec check', 'routine'):
            raise ValueError('unknown target kind')
        if row['status'] not in ('ok', 'not run', 'unconfirmed', 'timing unavailable'):
            raise ValueError('unknown measurement status')
        if row['status'] == 'ok':
            elapsed = row['elapsed']
            if (not math.isfinite(elapsed) or elapsed < 0
                    or not math.isclose(row['end'] - row['start'], elapsed, abs_tol=ROUNDING)):
                raise ValueError('invalid elapsed time')
    if not names:
        raise ValueError('empty manifest')


def complete(data):
    return data['proof_success'] and all(row['status'] == 'ok' for row in data['targets'])


def compatible(base, current):
    if not complete(base):
        return 'baseline proof timings incomplete'
    a, b = base['profile'], current['profile']
    absent = sorted(key for key in PROFILE_FIELDS if not a.get(key) or not b.get(key))
    if absent:
        return 'measurement profile missing ' + ', '.join(absent)
    different = sorted(key for key in PROFILE_FIELDS if a[key] != b[key])
    if different:
        return 'measurement profile differs in ' + ', '.join(different)
    return ''


def current_timings(api, run_id, sha, tree):
    result = {}
    for arch in ARCHES:
        try:
            found, problems = api.timings(arch, tree, run_id)
        except Unavailable as error:
            result[arch] = str(error)
            continue
        found = [data for data in found if data['sha'] == sha]
        result[arch] = found[0] if found else (problems + ['no timing artifact in this run'])[0]
    return result


def baseline_pending(api, sha):
    try:
        runs = api.list(f'workflows/{BASELINE_WORKFLOW}/runs', 'workflow_runs', head_sha=sha)
    except Unavailable:
        return False
    return any(run['status'] != 'completed' for run in runs)


def baseline_reports(api, base_sha, base_tree, current, run_id):
    """Pick, per architecture, the newest compatible timing of the base tree."""
    baselines, reasons = {}, {}
    for arch in ARCHES:
        if not isinstance(current[arch], dict):
            continue
        if not base_tree:
            reasons[arch] = 'tested merge base unavailable'
            continue
        try:
            found, problems = api.timings(arch, base_tree)
        except Unavailable as error:
            reasons[arch] = str(error)
            continue
        # A PR that changes no files has the base tree itself.
        for base in (data for data in found if data['run_id'] != run_id):
            problem = compatible(base, current[arch])
            if not problem:
                baselines[arch] = base
                break
            problems.append(problem)
        else:
            if problems:
                reasons[arch] = problems[0]
            elif baseline_pending(api, base_sha):
                reasons[arch] = 'baseline run in progress'
            else:
                reasons[arch] = 'no timings recorded for the base commit'
    return baselines, reasons


def missing(api, tree):
    """List the architectures with no complete timing of `tree` yet."""
    result = []
    for arch in ARCHES:
        try:
            found, _ = api.timings(arch, tree)
        except Unavailable:
            found = []
        if not any(complete(data) for data in found):
            result.append(arch)
    return result


def regression(before, after):
    return after >= 20 and after - before >= 10 and after >= 1.5 * before


def total_regression(before, after):
    return before > 0 and after >= 1.25 * before and after - before >= 60


def change(before, after):
    seconds = f'{after - before:+g} s'
    return f'{seconds} ({(after - before) / before:+.1%})' if before else seconds


def plural(count, noun):
    return f'{count} {noun}' + ('' if count == 1 else 's')


def duration(row):
    if row is None:
        return '—'
    if row['status'] != 'ok':
        return row['status']
    return f'{row["elapsed"]:g} s' if row['elapsed'] else '<1 s'


def table(rows, compared):
    header = ['| Proof | Status | PR | Base | Change |', '|-------|--------|----|------|--------|']
    if not compared:
        header = ['| Proof | Status | PR |', '|-------|--------|----|']
    return '\n'.join(header + ['| ' + ' | '.join(cells) + ' |' for cells in rows])


def section(arch, current, base, limit=None):
    """Return the regression rows and the folded table for one architecture."""
    new_rows = {row['target']: row for row in current['targets']}
    old_rows = {row['target']: row for row in base['targets']} if base else {}
    entries, alerts = [], []
    before_total = after_total = matched = untimed = 0
    for target in new_rows.keys() | old_rows.keys():
        new, old = new_rows.get(target), old_rows.get(target)
        name = f'`{target}`' + (' (spec check)' if (new or old)['kind'] == 'spec check' else '')
        if new is None:
            entries.append(((2, 0, target), [name, '—', '—', duration(old), 'removed']))
            continue
        if new['status'] != 'ok':
            untimed += 1
            cells = [name, FAIL, new['status']] + ([duration(old), '—'] if base else [])
            entries.append(((0, 0, target), cells))
            continue
        after = new['elapsed']
        cells = [name, OK, duration(new)]
        if base and old is None:
            cells += ['—', 'new']
        elif base:
            before = old['elapsed']
            cells += [duration(old), change(before, after)]
            if regression(before, after):
                cells[1] = WARN
                alerts.append((after - before, [f'{arch} {name}'] + cells[1:]))
        if new['kind'] == 'routine' and (not base or (old and old['kind'] == 'routine')):
            matched += 1
            after_total += after
            before_total += old['elapsed'] if base else 0
        entries.append(((1, -after, target), cells))

    # Totals cover the routines timed on both sides. Spec checks, added and
    # removed proofs are listed but left out.
    label = f'**TOTAL** ({plural(matched, "matched routine" if base else "routine")})'
    summary = f'{arch}: {plural(len(new_rows), "proof")}'
    if not complete(current):
        status = f'{untimed} without a time' if untimed else 'proof run failed'
        total = [label, FAIL, 'incomplete'] + (['—', '—'] if base else [])
        summary += f', incomplete ({status})'
    elif base:
        total = [label, OK, f'{after_total:g} s', f'{before_total:g} s',
                 change(before_total, after_total)]
        summary += f', total {after_total:g} s vs. base {before_total:g} s'
        if before_total:
            summary += f', {(after_total - before_total) / before_total:+.1%}'
        if total_regression(before_total, after_total):
            total[1] = WARN
            alerts.append((math.inf, [f'{arch} {label}'] + total[1:]))
    else:
        total = [label, OK, f'{after_total:g} s']
        summary += f', total {after_total:g} s'
    if alerts:
        summary += ' ' + WARN

    rows = [total] + [cells for _, cells in sorted(entries)]
    shown = rows if limit is None else rows[:limit + 1]
    lines = ['<details>', f'<summary>{summary}</summary>', '', table(shown, base)]
    if len(shown) < len(rows):
        lines += ['', f'Showing the first {limit} of {len(rows) - 1} proofs. '
                      'The job summary lists all of them.']
    phases = []
    for phase, name in (('build', 'build'), ('proof', 'proof run')):
        after = current['phases'].get(phase)
        before = base['phases'].get(phase) if base else None
        if after is not None:
            phases.append(f'{name} {before:g} s → {after:g} s' if before is not None
                          else f'{name} {after:g} s')
    if phases:
        lines += ['', 'Wall time, including tutorials: ' + ', '.join(phases) + '.']
    lines += ['', '</details>']
    return alerts, '\n'.join(lines)


def build_report(heading, current, baselines, reasons, limit=None):
    lines = [COMMENT_TAG, '## HOL Light proof times', '', heading]
    notes = {}
    for arch in ARCHES:
        if isinstance(current[arch], str):
            lines += ['', f'{FAIL} No {arch} timings: {current[arch]}.']
        elif arch not in baselines:
            notes.setdefault(reasons[arch], []).append(arch)
    for reason, arches in notes.items():
        lines += ['', f'{" and ".join(arches)} times are not compared: {reason}.']
    alerts, details = [], []
    for arch in ARCHES:
        if isinstance(current[arch], dict):
            found, text = section(arch, current[arch], baselines.get(arch), limit)
            alerts += found
            details.append(text)
    if alerts:
        rows = [cells for _, cells in sorted(alerts, key=lambda alert: -alert[0])]
        lines += ['', f'{WARN} **Attention required**', '', table(rows, True)]
    for text in details:
        lines += ['', text]
    return '\n'.join(lines) + '\n'


def pull_request_number():
    try:
        event = json.loads(Path(os.environ['GITHUB_EVENT_PATH']).read_text())
    except (KeyError, OSError, ValueError):
        return None
    return event.get('pull_request', {}).get('number')


def post_comment(api, number, body):
    """Create the PR's report comment, or update it in place on reruns."""
    path = f'repos/{api.repo}/issues/{number}/comments'
    pages = json.loads(api.gh('api', '--paginate', '--slurp', f'{path}?per_page=100'))
    ours = [comment['id'] for page in pages for comment in page
            if comment['user']['login'] == 'github-actions[bot]'
            and comment['body'].startswith(COMMENT_TAG)]
    with tempfile.NamedTemporaryFile('w', suffix='.json') as stream:
        json.dump({'body': body}, stream)
        stream.flush()
        if ours:
            api.gh('api', '--method', 'PATCH', f'repos/{api.repo}/issues/comments/{ours[0]}',
                   '--input', stream.name)
        else:
            api.gh('api', '--method', 'POST', path, '--input', stream.name)


def main():
    repo = os.environ['GITHUB_REPOSITORY']
    run_id = int(os.environ['GITHUB_RUN_ID'])
    sha = os.environ['GITHUB_SHA']
    parents = git('show', '-s', '--format=%P', sha).split()
    base_sha = parents[0] if len(parents) == 2 else None
    base_tree = git('rev-parse', base_sha + '^{tree}') if base_sha else None
    api = Actions(repo)
    current = current_timings(api, run_id, sha, git('rev-parse', sha + '^{tree}'))
    baselines, reasons = baseline_reports(api, base_sha, base_tree, current, run_id)

    run_url = f'{os.environ["GITHUB_SERVER_URL"]}/{repo}/actions/runs'
    heading = f'PR merge [`{sha[:12]}`]({run_url}/{run_id})'
    if base_sha:
        heading += f' vs. base `{base_sha[:12]}`'
    for base_run, attempt in sorted({(b['run_id'], b['attempt']) for b in baselines.values()}):
        heading += f' · [baseline run]({run_url}/{base_run}/attempts/{attempt})'
    report = build_report(heading, current, baselines, reasons)
    with open(os.environ['GITHUB_STEP_SUMMARY'], 'a') as stream:
        stream.write(report)

    number = pull_request_number()
    if number:
        if len(report) > COMMENT_LIMIT:
            report = build_report(heading, current, baselines, reasons, limit=50)
        try:
            post_comment(api, number, report)
        except Unavailable:
            # Fork PRs get a read-only token. The job summary has the report.
            print('Could not post the PR comment. The report is in the job summary.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--missing', action='store_true',
                        help='print a JSON list of the architectures with no complete '
                             'timing of HEAD\'s tree, then exit')
    if parser.parse_args().missing:
        print(json.dumps(missing(Actions(os.environ['GITHUB_REPOSITORY']),
                                 git('rev-parse', 'HEAD^{tree}'))))
    else:
        main()
