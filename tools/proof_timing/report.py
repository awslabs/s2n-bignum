"""Compare PR proof timings with saved timings for the tested base commit.

The proof-timing-report CI job runs `python3 tools/proof_timing/report.py`.
It writes per-proof timings to the job summary and flags regressions when
a compatible baseline is available.
"""

import json
import math
import os
from pathlib import Path
import re
import subprocess
import tempfile
from urllib.parse import urlencode

ARCHES = ('arm', 'x86')
BASELINE_WORKFLOW = 'proof-timing-baseline.yml'
BASELINE_EVENTS = ('push', 'workflow_dispatch')
PROFILE_FIELDS = {'host', 'cpu', 'available_cpus', 'image', 'os', 'hol_light',
                  'opam_packages', 'native_tools', 'build_jobs', 'proof_jobs'}
TARGET = re.compile(r'[A-Za-z0-9_/-]+\.correct')


class Unavailable(Exception):
    """A measurement or a piece of workflow metadata is unavailable."""


class Actions:
    def __init__(self, repo):
        self.repo = repo

    def gh(self, *args):
        result = subprocess.run(['gh', *args], capture_output=True, text=True)
        if result.returncode:
            # Keep the summary concise and the full CLI diagnostic in the job log.
            print(result.stderr.strip())
            raise Unavailable('GitHub Actions lookup failed (see report job log)')
        return result.stdout

    def list(self, path, key, **filters):
        query = urlencode(dict(per_page=100, **filters))
        pages = self.gh('api', '--paginate', '--slurp', f'repos/{self.repo}/actions/{path}?{query}')
        return [entry for page in json.loads(pages) for entry in page[key]]

    def report(self, run_id, arch, sha, job, artifacts):
        if not job or job['status'] != 'completed':
            raise Unavailable('proof job unavailable')
        attempt = job['run_attempt']
        name = f'proof-timing-{arch}-{attempt}'
        found = next((a for a in artifacts if a['name'] == name), None)
        if not found:
            raise Unavailable(f'proof job {job["conclusion"]}, artifact missing')
        if found['expired']:
            raise Unavailable('artifact expired')
        with tempfile.TemporaryDirectory() as directory:
            self.gh('run', 'download', str(run_id), '--repo', self.repo,
                    '--name', name, '--dir', directory)
            try:
                data = json.loads((Path(directory) / 'timing.json').read_text())
                validate(data, arch, sha, run_id, attempt)
            except (ValueError, KeyError, TypeError, AttributeError, OverflowError, OSError) as error:
                raise Unavailable(f'invalid timing artifact {name}') from error
        return data

    def reports(self, run_id, sha, attempt):
        # A report-only rerun can have a newer attempt than either proof job.
        # If a proof was rerun and failed to upload, don't reuse its old result.
        jobs = {}
        for job in self.list(f'runs/{run_id}/jobs', 'jobs', filter='all'):
            previous = jobs.get(job['name'])
            if job['run_attempt'] > attempt:
                continue
            if previous is None or job['run_attempt'] > previous['run_attempt']:
                jobs[job['name']] = job
        artifacts = self.list(f'runs/{run_id}/artifacts', 'artifacts')
        result = {}
        for arch in ARCHES:
            try:
                job = jobs.get(f's2n-bignum-proofs ({arch})')
                result[arch] = self.report(run_id, arch, sha, job, artifacts)
            except Unavailable as error:
                result[arch] = str(error)
        return result


def validate(data, arch, sha, run_id, attempt):
    identity = (data['version'], data['arch'], data['sha'], data['run_id'], data['attempt'])
    if identity != (1, arch, sha, run_id, attempt):
        raise ValueError('artifact identity mismatch')
    if not isinstance(data['profile'], dict) or not isinstance(data['proof_success'], bool):
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
            if not math.isfinite(row['elapsed']) or row['elapsed'] < 0 or row['elapsed'] != row['end'] - row['start']:
                raise ValueError('invalid elapsed time')
    if not names:
        raise ValueError('empty manifest')


def complete(data):
    return data['proof_success'] and all(row['status'] == 'ok' for row in data['targets'])


def compatible(base, current):
    if not complete(base):
        return 'baseline proof timings incomplete'
    a, b = base['profile'], current['profile']
    missing = sorted(key for key in PROFILE_FIELDS if not a.get(key) or not b.get(key))
    if missing:
        return 'measurement profile missing ' + ', '.join(missing)
    different = sorted(key for key in PROFILE_FIELDS if a[key] != b[key])
    if different:
        return 'measurement profile differs in ' + ', '.join(different)
    return ''


def baseline_reports(api, sha, current):
    remaining = {arch for arch in ARCHES if isinstance(current[arch], dict)}
    baselines = {}
    reasons = {}
    if not sha or not remaining:
        return baselines, dict.fromkeys(ARCHES, 'tested merge base unavailable')
    try:
        runs = api.list(f'workflows/{BASELINE_WORKFLOW}/runs', 'workflow_runs',
                        branch='main', head_sha=sha)
        for run in sorted(runs, key=lambda r: r['run_number'], reverse=True):
            if (run['repository']['full_name'] != api.repo or run['head_sha'] != sha
                    or run['head_branch'] != 'main' or run['event'] not in BASELINE_EVENTS):
                continue
            if run['status'] != 'completed' or run['conclusion'] != 'success':
                for arch in remaining:
                    reasons.setdefault(arch, 'baseline run ' + (run['conclusion'] or run['status']))
                continue
            candidates = api.reports(run['id'], sha, run['run_attempt'])
            for arch in remaining.copy():
                base = candidates[arch]
                problem = base if isinstance(base, str) else compatible(base, current[arch])
                if problem:
                    reasons.setdefault(arch, problem)
                else:
                    baselines[arch] = base
                    remaining.remove(arch)
            if not remaining:
                break
    except Unavailable as error:
        for arch in remaining:
            reasons.setdefault(arch, str(error))
    for arch in remaining:
        reasons.setdefault(arch, 'no baseline run for this commit')
    return baselines, reasons


def regression(before, after):
    return after >= 20 and after - before >= 10 and after >= 1.5 * before


def change(before, after):
    seconds = f'{after - before:+g} s'
    return f'{seconds} ({(after - before) / before:+.1%})' if before else seconds


def duration(row):
    if row is None:
        return '—'
    if row['status'] != 'ok':
        return row['status']
    return f'{row["elapsed"]:g} s' if row['elapsed'] else '<1 s'


def comparison(arch, current, base):
    current_rows = {row['target']: row for row in current['targets']}
    base_rows = {row['target']: row for row in base['targets']} if base else {}
    changes = []
    table = []
    before_total = after_total = 0
    matched = added = removed = unavailable = 0
    for target in sorted(current_rows.keys() | base_rows.keys()):
        old, new = base_rows.get(target), current_rows.get(target)
        label = ' — spec check' if (new or old)['kind'] == 'spec check' else ''
        delta = '—'
        if base and not old:
            delta = 'added'
            added += 1
        elif not new:
            delta = 'removed'
            removed += 1
        if new and new['status'] != 'ok':
            unavailable += 1
        if old and new and new['status'] == 'ok':
            before, after = old['elapsed'], new['elapsed']
            delta = change(before, after)
            warned = regression(before, after)
            if warned:
                delta += ' ⚠'
            if before != after:
                changes.append((after - before, target, delta, warned))
            if old['kind'] == new['kind'] == 'routine':
                matched += 1
                before_total += before
                after_total += after
        table.append(f'| `{target}`{label} | {duration(old)} | {duration(new)} | {delta} |')

    lines = []
    if base:
        warnings = sorted((c for c in changes if c[3]), reverse=True)
        count = len(warnings)
        lines.append(f'**{count} per-proof regression warning{"s" if count != 1 else ""}.**')
        lines.append(f'Matched {matched} routines · {added} added · {removed} removed · {unavailable} unavailable.')
        if matched and complete(current):
            total = f'Matched routine sum: {before_total:g} s → {after_total:g} s, {change(before_total, after_total)}.'
            if before_total and after_total >= 1.25 * before_total and after_total - before_total >= 60:
                total += ' ⚠'
                print(f'::warning::{arch} {total}')
            lines.append(total)
        else:
            lines.append('Matched routine sum unavailable.')
        for title, entries in [('Slowdowns', sorted(c for c in changes if c[0] > 0)[::-1]),
                               ('Speedups', sorted(c for c in changes if c[0] < 0))]:
            if entries:
                lines.append('**' + title + '**\n\n' + '\n'.join(
                    f'- `{name}` {delta}' for _, name, delta, _ in entries[:5]))
        for _, name, delta, _ in warnings[:5]:
            print(f'::warning::{arch}/{name} {delta}')
    if not complete(current):
        lines.append(f'Current proof run incomplete. Unavailable measurements: {unavailable}.')
    for phase in ('build', 'proof'):
        after = current['phases'].get(phase)
        before = base['phases'].get(phase) if base else None
        if after is not None:
            prefix = f'{before:g} s → ' if before is not None else ''
            lines.append(f'{phase.capitalize()} phase wall time (includes tutorials): {prefix}{after:g} s.')
    lines.extend(['<details><summary>All proof targets</summary>',
                  '| Target | Base | PR | Change |\n|---|---:|---:|---|\n' + '\n'.join(table), '</details>'])
    return '\n\n'.join(lines)


def main():
    repo = os.environ['GITHUB_REPOSITORY']
    run_id = int(os.environ['GITHUB_RUN_ID'])
    sha = os.environ['GITHUB_SHA']
    parents = subprocess.check_output(['git', 'show', '-s', '--format=%P', sha], text=True).split()
    base_sha = parents[0] if len(parents) == 2 else None
    api = Actions(repo)
    try:
        current = api.reports(run_id, sha, int(os.environ['GITHUB_RUN_ATTEMPT']))
    except Unavailable as error:
        current = dict.fromkeys(ARCHES, str(error))
    baselines, reasons = baseline_reports(api, base_sha, current)
    run_url = f'{os.environ["GITHUB_SERVER_URL"]}/{repo}/actions/runs'
    summary = ['# Proof times', f'PR merge [`{sha[:12]}`]({run_url}/{run_id}) · Tested base `{base_sha or "unknown"}`.']
    for arch in ARCHES:
        summary.append(f'## {arch}')
        if isinstance(current[arch], str):
            summary.append('Current timings unavailable: ' + current[arch] + '.')
            continue
        base = baselines.get(arch)
        if base:
            summary.append(f'[Baseline run]({run_url}/{base["run_id"]}/attempts/{base["attempt"]})')
        else:
            summary.append('Comparison unavailable: ' + reasons[arch] + '.')
        summary.append(comparison(arch, current[arch], base))
    with open(os.environ['GITHUB_STEP_SUMMARY'], 'a') as stream:
        stream.write('\n\n'.join(summary) + '\n')


if __name__ == '__main__':
    main()
