"""Compare PR proof timings with saved timings for the tested base commit.

Timing artifacts are named after the git tree they measured, so any run
that tested the base commit's files can serve as the baseline.

The proof-timing-report CI job runs `python3 tools/proof_timing/report.py`.
It writes full timing tables to the job summary and to one PR comment,
updated in place on reruns. `--slowest` and `--min-seconds` limit both
reports to the slowest proofs, by the slower of their base and PR times.
Major changes highlight regressions and improvements, with a warning for
each architecture whose measurement profiles differ. The baseline workflow
uses `--missing` to decide which architectures still need a proof run.
"""

import argparse
from dataclasses import dataclass
from html import escape
import json
import math
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from urllib.parse import urlencode

ARCHES = {'arm': 'ARM', 'x86': 'x86'}
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


def cpu_models(before, after):
    # Drop lscpu boilerplate while keeping a difference in clock speed visible.
    models = [re.sub(r'^Intel\(R\) |\(R\)| CPU @ [\d.]+GHz$', '', str(cpu)) for cpu in (before, after)]
    if models[0] == models[1]:
        models = [str(before), str(after)]
    return ' vs '.join(' '.join(model.split()) for model in models)


def profile_differences(base, current):
    notes = []
    for key in sorted(PROFILE_FIELDS):
        before, after = base['profile'].get(key), current['profile'].get(key)
        label = 'CPU' if key == 'cpu' else key
        if not before or not after:
            notes.append(f'{label} not recorded')
        elif before != after:
            note = f'{label} differs'
            if key == 'cpu':
                note += f' ({cpu_models(before, after)})'
            notes.append(note)
    return notes


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
    """Prefer a complete profile match, then a complete run, then partial timings."""
    baselines = {}
    for arch in ARCHES:
        if not base_tree:
            baselines[arch] = 'tested merge base unavailable'
            continue
        try:
            found, problems = api.timings(arch, base_tree)
        except Unavailable as error:
            baselines[arch] = str(error)
            continue
        # A PR that changes no files has the base tree itself.
        candidates = [data for data in found if data['run_id'] != run_id]
        if candidates:
            finished = [base for base in candidates if complete(base)]
            pr = current[arch]
            baselines[arch] = (finished or candidates)[0]
            if isinstance(pr, dict):
                for base in finished:
                    if not profile_differences(base, pr):
                        baselines[arch] = base
                        break
        elif problems:
            baselines[arch] = problems[0]
        elif baseline_pending(api, base_sha):
            baselines[arch] = 'baseline run in progress'
        else:
            baselines[arch] = 'no timings recorded for the base commit'
    return baselines


def keep(data, names):
    if not isinstance(data, dict):
        return data
    return dict(data, targets=[row for row in data['targets'] if row['target'] in names])


def select_proofs(current, base, count, min_seconds):
    """Keep the PR's `count` slowest proofs that took at least `min_seconds`.

    A proof's time is the slower of its base and PR times, so whether a
    proof is kept does not depend on whether it got faster or slower.
    Proofs that neither run timed are dropped. Without filters, all PR
    proofs are kept. The baseline keeps the same proofs.
    """
    rows = current['targets'] if isinstance(current, dict) else []
    names = [row['target'] for row in rows]
    if count is not None or min_seconds is not None:
        old = {row['target']: row for row in base['targets']} if isinstance(base, dict) else {}
        times = {}
        for row in rows:
            seconds = [side['elapsed'] for side in (row, old.get(row['target']))
                       if side and side['status'] == 'ok']
            if seconds and max(seconds) >= (min_seconds or 0):
                times[row['target']] = max(seconds)
        names = sorted(times, key=lambda name: (-times[name], name))[:count]
    return keep(current, set(names)), keep(base, set(names))


def scope_note(count, min_seconds):
    if count is None and min_seconds is None:
        return ''
    note = 'Showing, per architecture, the ' + (f'{count} slowest ' if count is not None else '') + 'proofs'
    if min_seconds is not None:
        note += f' that took at least {min_seconds:g} s'
    return note + ', by the slower of their base and PR times.'


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
    delta = after - before
    seconds = f'{delta:+,g} s'
    result = f'{seconds} ({delta / before:+.1%})' if before else seconds
    return result.replace('-', '−')


def plural(count, noun):
    return f'{count} {noun}' + ('' if count == 1 else 's')


def duration(row):
    if row is None:
        return '—'
    if row['status'] != 'ok':
        return row['status']
    return f'{row["elapsed"]:,g} s' if row['elapsed'] else '<1 s'


def table_row(*cells):
    return '| ' + ' | '.join(cells) + ' |'


def add_major_change(alerts, arch, name, before, after, *, total=False):
    threshold = total_regression if total else regression
    if threshold(before, after):
        direction = 'Regression'
    elif threshold(after, before):
        direction = 'Improvement'
    else:
        return
    row = table_row(f'{arch} {name}', direction, f'{before:,g} s', f'{after:,g} s', change(before, after))
    alerts.append(((not total, -abs(after - before), arch, name), row))


def phase_times(base, current):
    phases = []
    for phase, name in [('build', 'build'), ('proof', 'proof run')]:
        times = [data['phases'].get(phase) if isinstance(data, dict) else None
                 for data in (base, current)]
        if any(value is not None for value in times):
            values = ['—' if value is None else f'{value:g} s' for value in times]
            phases.append(name + ' ' + ' → '.join(values))
    return 'Wall time, including tutorials (Base → PR): ' + ', '.join(phases) + '.' if phases else ''


def routine_sum(finished, rows, names):
    if finished and names:
        return sum(rows[name]['elapsed'] for name in names)
    return None


@dataclass
class ReportTable:
    title: str
    rows: list
    folded: bool = True
    note: str = ''
    intro: str = ''

    def render(self):
        if self.folded:
            lines = ['<details>', f'<summary>{escape(self.title)}</summary>']
            columns = ('Proof', 'Status')
        else:
            lines = [f'### {self.title}']
            columns = ('Architecture / proof', 'Direction')
        if self.intro:
            lines.extend(['', escape(self.intro)])
        if self.rows or self.folded:
            lines.extend(['', table_row(*columns, 'Base', 'PR', 'Observed change (PR − Base)'),
                          '|---|---|---:|---:|---:|', *self.rows])
        if self.note:
            lines.extend(['', self.note])
        if self.folded:
            lines.extend(['', '</details>'])
        return '\n'.join(lines)


def section(arch, current, base):
    """Collect the full table and major changes for one architecture.

    The table lists the PR's proofs. Baseline proofs the PR lacks are ignored.
    """
    arch = ARCHES[arch]
    notes = []
    base_complete = isinstance(base, dict) and complete(base)
    pr_complete = isinstance(current, dict) and complete(current)
    for label, data, finished in [('Base', base, base_complete), ('PR', current, pr_complete)]:
        if isinstance(data, str):
            notes.append(f'{label} unavailable ({data})')
        elif not finished:
            notes.append(f'{label} incomplete')
    both = isinstance(base, dict) and isinstance(current, dict)
    if both:
        differences = profile_differences(base, current)
        notes.append('⚠️ ' + ', '.join(differences) if differences else 'Profiles match')

    old_rows = {row['target']: row for row in base['targets']} if isinstance(base, dict) else {}
    new_rows = {row['target']: row for row in current['targets']} if isinstance(current, dict) else {}
    title = ' · '.join(['Full results', arch, plural(len(new_rows), 'proof'), *notes])
    if not new_rows:
        return ReportTable(title, [], note='No proof timings available.'), [], False
    alerts = []
    entries = []
    paired = False

    for target, new in new_rows.items():
        old = old_rows.get(target)
        name = f'`{target}`' + (' (spec check)' if new['kind'] == 'spec check' else '')
        status, delta = 'Timed', '—'
        untimed = any(row and row['status'] != 'ok' for row in (old, new))
        if both and old is None:
            status = 'Added'
        elif untimed:
            status = 'Incomplete'
        elif old:
            before, after = old['elapsed'], new['elapsed']
            delta = change(before, after)
            paired = True
            add_major_change(alerts, arch, name, before, after)
        row = table_row(name, status, duration(old), duration(new), delta)
        entries.append(((not untimed, 0 if untimed else -new['elapsed'], target), row))

    old_routines = {name for name, row in old_rows.items() if row['kind'] == 'routine'}
    new_routines = {name for name, row in new_rows.items() if row['kind'] == 'routine'}
    names = old_routines & new_routines if both else new_routines
    label = '**Total** (' + plural(len(names), 'matched routine' if both else 'routine') + ')'
    before, after = routine_sum(base_complete, old_rows, names), routine_sum(pr_complete, new_rows, names)
    total_status, delta = 'Incomplete', '—'
    if before is not None and after is not None:
        total_status = 'Complete'
        delta = change(before, after)
        add_major_change(alerts, arch, label, before, after, total=True)
    elif base_complete and pr_complete:
        total_status = 'No matched routines'
    elif not both and pr_complete:
        total_status = 'Base unavailable'
    times = ['—' if value is None else f'{value:,g} s' for value in (before, after)]
    rows = [table_row(label, total_status, *times, delta)]
    rows.extend(row for _, row in sorted(entries))
    return ReportTable(title, rows, note=phase_times(base, current)), alerts, paired


def build_report(current, baselines):
    details, alerts, comparable, warnings = [], [], [], []
    for arch in ARCHES:
        pr, base = current[arch], baselines[arch]
        table, changes, paired = section(arch, pr, base)
        details.append(table)
        alerts.extend(changes)
        if paired:
            comparable.append(ARCHES[arch])
        if isinstance(pr, dict) and isinstance(base, dict) and profile_differences(base, pr):
            warnings.append(f'⚠️ {ARCHES[arch]}: ' + ', '.join(profile_differences(base, pr)))
    note = ''
    if not alerts:
        note = ('No major changes for ' + ' and '.join(comparable) + '.' if comparable
                else 'No architecture has comparable timings.')
    major = ReportTable('Major changes', [row for _, row in sorted(alerts)], folded=False,
                        note=note, intro='\n\n'.join(warnings))
    return [major, *details]


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


def main(args):
    repo = os.environ['GITHUB_REPOSITORY']
    run_id = int(os.environ['GITHUB_RUN_ID'])
    sha = os.environ['GITHUB_SHA']
    parents = git('show', '-s', '--format=%P', sha).split()
    base_sha = parents[0] if len(parents) == 2 else None
    base_tree = git('rev-parse', base_sha + '^{tree}') if base_sha else None
    api = Actions(repo)
    current = current_timings(api, run_id, sha, git('rev-parse', sha + '^{tree}'))
    baselines = baseline_reports(api, base_sha, base_tree, current, run_id)
    for arch in ARCHES:
        current[arch], baselines[arch] = select_proofs(current[arch], baselines[arch],
                                                       args.slowest, args.min_seconds)

    run_url = f'{os.environ["GITHUB_SERVER_URL"]}/{repo}/actions/runs'
    heading = f'PR merge [`{sha[:12]}`]({run_url}/{run_id})'
    if base_sha:
        heading += f' vs. base `{base_sha[:12]}`'
    sources = {}
    for arch, base in baselines.items():
        if isinstance(base, dict):
            sources.setdefault((base['run_id'], base['attempt']), []).append(ARCHES[arch])
    for (base_run, attempt), arches in sources.items():
        heading += f' · [{"/".join(arches)} baseline run]({run_url}/{base_run}/attempts/{attempt})'
    heading = '## HOL Light proof times\n\n' + heading
    if scope_note(args.slowest, args.min_seconds):
        heading += '\n\n' + scope_note(args.slowest, args.min_seconds)
    tables = build_report(current, baselines)
    report = '\n\n'.join([COMMENT_TAG + '\n' + heading, *(table.render() for table in tables)]) + '\n'
    with open(os.environ['GITHUB_STEP_SUMMARY'], 'a') as stream:
        stream.write(report)

    number = pull_request_number()
    if number:
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
    parser.add_argument('--slowest', type=int, metavar='N',
                        help='report only the N slowest proofs per architecture, by the '
                             'slower of their base and PR times')
    parser.add_argument('--min-seconds', type=float, metavar='Y',
                        help='report only proofs whose base or PR run took at least Y seconds')
    args = parser.parse_args()
    if args.missing:
        print(json.dumps(missing(Actions(os.environ['GITHUB_REPOSITORY']),
                                 git('rev-parse', 'HEAD^{tree}'))))
    else:
        main(args)
