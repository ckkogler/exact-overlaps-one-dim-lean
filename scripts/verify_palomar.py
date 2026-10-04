#!/usr/bin/env python3
"""Run strict Comparator with Lean's kernel, NanoDa and con-ron in its sandbox.

Requires the repository's pinned Lean toolchain and bubblewrap 0.12.0.
Set COMPARATOR_BWRAP if bubblewrap is not on PATH. No registry request is made.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepare-only', action='store_true')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    env = os.environ.copy()
    for name in ['ELAN_TOOLCHAIN', 'LEAN_PATH', 'MATHLIB_CACHE_DIR']:
        env.pop(name, None)
    expected = (root / 'lean-toolchain').read_text().strip()
    assert expected == 'leanprover/lean4:v4.35.0-rc2', expected
    prefix = Path(subprocess.check_output(
        ['lean', '--print-prefix'], cwd=root, env=env, text=True).strip())
    version = subprocess.check_output([str(prefix / 'bin/lean'), '--version'], text=True)
    assert '4.35.0-rc2' in version and '11acb17ec6b07a8f9e9173e6845197929540936b' in version
    binaries = {name: prefix / 'bin' / name for name in
                ['lake', 'lean', 'leanexport', 'leanchecker', 'nanoda_bin', 'con-ron']}
    for name, path in binaries.items():
        assert path.is_file() and os.access(path, os.X_OK), name
        print(name, hashlib.sha256(path.read_bytes()).hexdigest(), flush=True)
    env['PATH'] = str(prefix / 'bin') + os.pathsep + env.get('PATH', '')
    bwrap = shutil.which(env.get('COMPARATOR_BWRAP', 'bwrap'), path=env['PATH'])
    assert bwrap, 'Install bubblewrap 0.12.0 or set COMPARATOR_BWRAP.'
    assert subprocess.check_output([bwrap, '--version'], text=True).strip() == 'bubblewrap 0.12.0'
    env['COMPARATOR_BWRAP'] = bwrap
    print('bubblewrap', hashlib.sha256(Path(bwrap).read_bytes()).hexdigest(), flush=True)
    config = json.loads((root / 'comparator.json').read_text())
    config.pop('enable_nanoda', None)
    assert set(config['permitted_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
    assert config['theorem_names'] and len(config['theorem_names']) == len(set(config['theorem_names']))
    config['external_kernels'] = {
        'nanoda': [str(binaries['nanoda_bin'])],
        'con-ron': [str(binaries['con-ron'])],
    }
    generated = root / '.lake' / 'palomar-comparator.json'
    generated.parent.mkdir(parents=True, exist_ok=True)
    generated.write_text(json.dumps(config, indent=2) + '\n')
    if args.prepare_only:
        print('Verifier preparation passed; comparison has not been run.', flush=True)
        return
    subprocess.run([str(binaries['lake']), 'comparator', '--config', str(generated)],
                   cwd=root, env=env, check=True)


if __name__ == '__main__':
    main()
