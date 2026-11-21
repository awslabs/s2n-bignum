"""Read proof logs and completion markers for one architecture into timing JSON.

After the proof step, the proofs action runs
`python3 tools/proof_timing/collect.py "$PROOF_ARCH" "$RUNNER_TEMP/timing.json"`
and uploads the file as a workflow artifact.
"""

import argparse
import json
import math
import os
from pathlib import Path
import platform
import re
import subprocess

NUMBER = r"(\d+(?:\.\d+)?)"
TIMING = re.compile(rf"Running time: {NUMBER} sec, Start unixtime: {NUMBER}, End unixtime: {NUMBER}")


def output(*args, cwd=None):
    return subprocess.check_output(args, cwd=cwd, text=True).strip()


def measurement_profile(holdir):
    # The proof builder uses the local HOL Light opam switch. Its package
    # versions can change independently of the HOL Light and s2n revisions.
    cpu = dict(line.split(':', 1) for line in output('env', 'LC_ALL=C', 'lscpu').splitlines() if ':' in line)
    return {
        'host': platform.machine(),
        'cpu': cpu.get('Model name', '').strip(),
        'available_cpus': output('nproc'),
        'image': os.environ.get('CODEBUILD_BUILD_IMAGE'),
        'os': Path('/etc/os-release').read_text().strip(),
        'hol_light': output('git', 'rev-parse', 'HEAD', cwd=holdir),
        'opam_packages': output('opam', 'list', '--installed', '--short',
                                '--columns=package', '--color=never', cwd=holdir).splitlines(),
        'native_tools': output('dpkg-query', '-W', 'gcc', 'binutils',
                               'binutils-aarch64-linux-gnu', 'binutils-x86-64-linux-gnu'),
        'build_jobs': int(os.environ['BUILD_JOBS']),
        'proof_jobs': int(os.environ['PROOF_JOBS']),
    }


def read_timing(arch, target, markers):
    row = {'target': target, 'kind': 'spec check' if target.startswith('proofs/') else 'routine'}
    path = arch / target
    if not (markers / arch / target).is_file():
        row['status'] = 'unconfirmed' if path.exists() else 'not run'
        return row
    row['status'] = 'timing unavailable'
    if path.is_file():
        with path.open(errors='replace') as stream:
            lines = [line.rstrip('\n') for line in stream if line.startswith('Running time:')]
        match = TIMING.fullmatch(lines[0]) if len(lines) == 1 else None
        if match:
            elapsed, start, end = map(float, match.groups())
            if math.isfinite(elapsed) and end - start == elapsed:
                row.update(status='ok', elapsed=elapsed, start=start, end=end)
    return row


def collect(arch, destination):
    holdir = os.environ['HOLDIR']
    targets = output('make', '-s', '--no-print-directory', 'proof-timing-targets', cwd=arch).splitlines()
    if not targets or len(set(targets)) != len(targets):
        raise ValueError('empty or duplicate proof manifest')
    report = {
        'version': 1, 'arch': str(arch), 'sha': output('git', 'rev-parse', 'HEAD'),
        'run_id': int(os.environ['GITHUB_RUN_ID']), 'attempt': int(os.environ['GITHUB_RUN_ATTEMPT']),
        'profile': {}, 'phases': {},
    }
    try:
        report['profile'] = measurement_profile(holdir)
    except (OSError, subprocess.CalledProcessError) as error:
        print(f'::warning::Timing profile unavailable: {error}', flush=True)

    markers = Path(os.environ['PROOF_TIMING_MARKERS'])
    report['proof_success'] = os.environ['PROOF_OUTCOME'] == 'success'
    for phase in ('build', 'proof'):
        duration = os.environ.get(phase.upper() + '_SECONDS')
        if duration:
            report['phases'][phase] = int(duration)
    report['targets'] = [read_timing(arch, target, markers) for target in targets]
    destination.write_text(json.dumps(report, indent=2, allow_nan=False) + '\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('arch', choices=['arm', 'x86'])
    parser.add_argument('destination', type=Path)
    args = parser.parse_args()
    collect(Path(args.arch), args.destination)
