#!/usr/bin/env python3
"""Replay the concrete construction companions with three bundled Lean kernels."""
import argparse
import hashlib
import json
import re
import subprocess
import time
from pathlib import Path


def digest(path):
    result = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            result.update(block)
    return result.hexdigest()


def fingerprint(source):
    paths = sorted(source.glob('Controller/**/*.lean'))
    paths += [source / 'Phase1/Audit/Construction.lean']
    paths += [source / name for name in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
                                         'provenance/construction-audit-targets.json']]
    return {str(path.relative_to(source)): digest(path) for path in paths}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    source, output = args.source.resolve(), args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    targets = json.loads((source / 'provenance/construction-audit-targets.json').read_text())
    assert set(targets['permitted_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
    names = targets['declarations']
    assert names and len(names) == len(set(names))
    assert all(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*', name) for name in names)
    assert (source / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0-rc3'
    inputs = fingerprint(source)
    prefix = Path(subprocess.check_output(['lake', 'env', 'lean', '--print-prefix'],
                                         cwd=source, text=True).strip())
    binary = prefix / 'bin'
    policy = prefix / 'src/lean/lake/Lake/CLI/Check.lean'
    policy_text = policy.read_text()
    start = policy_text.index('def primitiveTargets')
    end = policy_text.index('\n\ndef ', start + 1)
    primitive_names = re.findall(r'(?m)^    ``([A-Za-z0-9_.]+)', policy_text[start:end])
    assert primitive_names and 'Nat.add' in primitive_names
    report = {'status': 'RUNNING_LOCAL_KERNEL_REPLAY', 'source': str(source),
              'module': targets['module'], 'declarations': names, 'input_sources': inputs,
              'toolchain_prefix': str(prefix), 'primitive_policy_sha256': digest(policy),
              'primitive_targets': primitive_names, 'checks': [],
              'protected_Linux_rehearsal': False, 'published': False}

    def run(name, command, stdout=None):
        assert fingerprint(source) == inputs, 'source changed during replay'
        started = time.monotonic()
        log = output / (name + '.log')
        print('START', name, flush=True)
        with log.open('w') as errors:
            if stdout is None:
                result = subprocess.run(command, cwd=source, stdout=errors,
                                        stderr=subprocess.STDOUT)
            else:
                with stdout.open('wb') as stream:
                    result = subprocess.run(command, cwd=source, stdout=stream, stderr=errors)
        row = {'name': name, 'command': command, 'exit_code': result.returncode,
               'seconds': round(time.monotonic() - started, 3), 'log': str(log),
               'log_sha256': digest(log)}
        report['checks'].append(row)
        (output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
        if result.returncode:
            raise SystemExit(f'{name} failed; inspect {log}')
        assert fingerprint(source) == inputs, 'source changed during replay'
        print('PASS', name, flush=True)

    exported = output / 'construction.export'
    run('export', ['lake', 'env', str(binary / 'leanexport'), targets['module'], '--',
                   *names, *primitive_names], stdout=exported)
    report['export_sha256'] = digest(exported)
    report['export_bytes'] = exported.stat().st_size
    settings = output / 'nanoda.json'
    settings.write_text(json.dumps({'use_stdin': False, 'export_file_path': str(exported),
        'permitted_axioms': targets['permitted_axioms'], 'unpermitted_axiom_hard_error': False,
        'num_threads': 4, 'nat_extension': True, 'string_extension': True}, indent=2) + '\n')
    for label, command in [
        ('con-ron', [str(binary / 'con-ron'), '--jobs=4', str(exported)]),
        ('NanoDa', [str(binary / 'nanoda_bin'), str(settings)]),
        ('Lean-default', [str(binary / 'leanchecker'), '--silent', '--from-export', str(exported)]),
    ]:
        report.setdefault('kernel_binaries', {})[label] = {
            'path': command[0], 'sha256': digest(Path(command[0]))}
        run(label, command)
    report['status'] = 'LOCAL_COMPANION_EXPORT_THREE_KERNELS_PASS'
    (output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(report['status'], flush=True)


if __name__ == '__main__':
    main()
