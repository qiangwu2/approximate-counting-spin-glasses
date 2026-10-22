#!/usr/bin/env python3
"""Recompile every local proof, audit all axioms, and test the audit's rejection.

Verification success requires the actual final accuracy-and-cost endpoints,
the stated counting corollaries, complete local import coverage, and a clean
transitive axiom audit. Mathematical source correspondence is recorded separately.
"""
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]
os.chdir(ROOT)
# Clear any previous success before preflight, so every failure is fail-closed.
preflight_status_path = ROOT / 'verification-status.json'
preflight_status_path.write_text(json.dumps({
    'verification_status': 'RUNNING',
    'kernel_verification_passed': False,
    'unconditional_end_to_end_program_certified': False,
    'phase': 'PREFLIGHT',
    'started_utc': datetime.now(timezone.utc).isoformat()}, indent=2) + '\n')
try:
    LAKE = shutil.which('lake')
    if not LAKE:
        candidate = Path.home() / '.elan/bin/lake'
        if candidate.exists():
            LAKE = str(candidate)
    if not LAKE:
        raise SystemExit('Lake is unavailable; install Elan/Lean and the pinned dependencies.')

    def digest(p):
        return hashlib.sha256(p.read_bytes()).hexdigest()

    sources = sorted([ROOT / 'Manuscript.lean', *ROOT.glob('Manuscript/**/*.lean'),
                      *ROOT.glob('SpinGlass/**/*.lean'), ROOT / 'Audit.lean'])
    config = [ROOT / 'lean-toolchain', ROOT / 'lakefile.toml', ROOT / 'lake-manifest.json',
              Path(__file__).resolve(), ROOT / 'scripts/DeclarationClosure.lean', ROOT / 'checks/check_sk.py',
              ROOT / 'source-provenance.json', ROOT / 'manuscript-map.json',
              ROOT / 'current-audit-additions.json',
              ROOT / 'paper/main-12-2-2.tex', ROOT / 'paper/references-2.bib']
    source_map = json.loads((ROOT / 'manuscript-map.json').read_text())
    if source_map['formal_coverage_status'].get('source_correspondence_review_complete') is not True:
        raise SystemExit('Source correspondence review is not marked complete.')
    paper_text = (ROOT / 'paper/main-12-2-2.tex').read_text()
    numbered_labels = set(re.findall(
        r'\\begin\{(?:theorem|lemma|proposition)\}(?:\[[^\]]*\])?\s*\\label\{([^}]+)\}', paper_text))
    mapped_labels = {entry.get('tex_label') for entry in source_map['coverage']}
    if not numbered_labels or not numbered_labels <= mapped_labels:
        raise SystemExit('Numbered manuscript statements missing from source map: ' +
                         str(numbered_labels - mapped_labels))
    paper_digest = digest(ROOT / 'paper/main-12-2-2.tex')
    if paper_digest != source_map['source_tex_sha256']:
        raise SystemExit('The bundled manuscript does not match the reviewed source hash.')
    additions = json.loads((ROOT / 'current-audit-additions.json').read_text())
    for entry in additions['additions']:
        if digest(ROOT / entry['file']) != entry['sha256']:
            raise SystemExit('Current proof manifest hash mismatch: ' + entry['file'])
    before = {str(p.relative_to(ROOT)): digest(p) for p in sources + config}
    modules = {str(p.relative_to(ROOT).with_suffix('')).replace('/', '.'): p
               for p in sources if p.name != 'Audit.lean'}
    all_imports = {name: set(re.findall(r'^import\s+([\w.]+)', p.read_text(), re.M))
                   for name, p in modules.items()}
    for name, imports in all_imports.items():
        missing = {d for d in imports if d.startswith(('Manuscript.', 'SpinGlass.')) and d not in modules}
        if missing:
            raise SystemExit(f'Missing local proof sources imported by {name}: {sorted(missing)}')
    deps = {name: imports & modules.keys() for name, imports in all_imports.items()}

    reachable = set()
    def visit(n):
        if n in reachable:
            return
        reachable.add(n)
        for d in deps[n]:
            visit(d)
    visit('Manuscript')
    if reachable != set(modules):
        raise SystemExit('Unimported local proof modules: ' + str(set(modules) - reachable))

    status = {'verification_status': 'RUNNING', 'kernel_verification_passed': False,
              'coverage_status': 'AWAITING_FRESH_VERIFICATION',
              'unconditional_end_to_end_program_certified': False,
              'source_sha256': before, 'manuscript_tex_sha256': paper_digest,
              'correspondence_assessment': source_map['formal_coverage_status'],
              'started_utc': datetime.now(timezone.utc).isoformat()}
    status_path = ROOT / 'verification-status.json'
    status_path.write_text(json.dumps(status, indent=2) + '\n')

    def compile_module(name):
        path = modules[name]
        dest = ROOT / '.lake/build/lib/lean' / Path(*name.split('.'))
        dest.parent.mkdir(parents=True, exist_ok=True)
        command = [LAKE, 'env', 'lean', '-o', str(dest.with_suffix('.olean')),
                   '-i', str(dest.with_suffix('.ilean')), str(path.relative_to(ROOT))]
        p = subprocess.run(command, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        return name, p.returncode, p.stdout

    try:
        completed = set()
        logs = []
        workers = max(1, min(4, int(os.environ.get('LEAN_VERIFY_JOBS', '3'))))
        while len(completed) < len(modules):
            ready = sorted(n for n in modules if n not in completed and deps[n] <= completed)
            if not ready:
                raise RuntimeError('Local import cycle detected.')
            with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
                for name, rc, out in pool.map(compile_module, ready):
                    logs.append(f'MODULE {name}\nEXIT {rc}\n{out}')
                    print(f'{"PASS" if rc == 0 else "FAIL"} {name}', flush=True)
                    if rc != 0:
                        raise RuntimeError(f'Compilation failed for {name}:\n{out}')
                    completed.add(name)
            (ROOT / 'verification.log').write_text('\n'.join(logs))

        def mapped_names(obj):
            if isinstance(obj, dict):
                for key, value in obj.items():
                    if key == 'declaration':
                        for name in value.split(';'):
                            name = name.strip()
                            if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*', name):
                                raise RuntimeError('Invalid source-map declaration name: ' + name)
                            yield name
                    else:
                        yield from mapped_names(value)
            elif isinstance(obj, list):
                for value in obj:
                    yield from mapped_names(value)
        map_names = sorted(set(mapped_names(source_map)))
        with tempfile.TemporaryDirectory(prefix='manuscript-map-check-') as tmp:
            mapped = Path(tmp) / 'SourceMapCheck.lean'
            mapped.write_text('import Manuscript\n' + ''.join('#check ' + n + '\n' for n in map_names))
            result = subprocess.run([LAKE, 'env', 'lean', str(mapped)], text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            (ROOT / 'source-map-check.log').write_text(result.stdout)
            if result.returncode != 0:
                raise RuntimeError('Source-map declaration check failed:\n' + result.stdout)

        audit = subprocess.run([LAKE, 'env', 'lean', 'Audit.lean'], text=True,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (ROOT / 'axiom-audit.log').write_text(audit.stdout)
        if audit.returncode != 0 or 'AXIOM AUDIT PASSED:' not in audit.stdout:
            raise RuntimeError('Axiom audit failed:\n' + audit.stdout)
        summary = re.search(r'AXIOM AUDIT PASSED: (\d+) theorem declarations; '
                            r'(\d+) total declarations; (\d+) manuscript theorem declarations',
                            audit.stdout)
        if not summary:
            raise RuntimeError('Audit success output is missing its declaration counts.')

        closure = subprocess.run([LAKE, 'env', 'lean', 'scripts/DeclarationClosure.lean'], text=True,
                                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (ROOT / 'declaration-closure.log').write_text(closure.stdout)
        if closure.returncode != 0 or closure.stdout.count('CLOSURE ') != 8:
            raise RuntimeError('Independent declaration closure audit failed:\n' + closure.stdout)
        closure_lines = [line for line in closure.stdout.splitlines() if line.startswith('CLOSURE ')]
        (ROOT / 'dependency-summary.json').write_text(json.dumps({
            'status': 'PASSED', 'roots': 8, 'summaries': closure_lines,
            'allowed_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
            'unsafe_or_missing_dependencies': []}, indent=2) + '\n')

        audit_text = (ROOT / 'Audit.lean').read_text()
        cut = audit_text.index('open Lean Elab Command in')
        fixtures = {
            'custom_axiom': 'namespace Manuscript.AuditFixture\naxiom bogus : False\nend Manuscript.AuditFixture\n',
            'public_placeholder': 'namespace Manuscript.AuditFixture\ntheorem bogus : False := by sorry\nend Manuscript.AuditFixture\n',
            'private_placeholder': 'namespace Manuscript.AuditFixture\nprivate theorem bogus : False := by sorry\nend Manuscript.AuditFixture\n',
            'outside_namespace_axiom': 'namespace UnrelatedNamespace\naxiom bogus : False\nend UnrelatedNamespace\n',
        }
        self_logs = []
        with tempfile.TemporaryDirectory(prefix='manuscript-axiom-audit-') as tmp:
            for name, fixture in fixtures.items():
                p = Path(tmp) / (name + '.lean')
                p.write_text(audit_text[:cut] + fixture + '\n' + audit_text[cut:])
                result = subprocess.run([LAKE, 'env', 'lean', str(p)], text=True,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                rejected = result.returncode != 0 and 'Disallowed axiom' in result.stdout
                self_logs.append(f'{name}: {"REJECTED AS EXPECTED" if rejected else "FAILED"}\n'
                                 + '\n'.join(l for l in result.stdout.splitlines()
                                             if 'Disallowed axiom' in l))
                if not rejected:
                    raise RuntimeError('Audit failed to reject ' + name + ':\n' + result.stdout)
        (ROOT / 'audit-self-check.log').write_text('\n'.join(self_logs) + '\n')
        final_sources = sorted([ROOT / 'Manuscript.lean', *ROOT.glob('Manuscript/**/*.lean'),
                                *ROOT.glob('SpinGlass/**/*.lean'), ROOT / 'Audit.lean'])
        if final_sources != sources:
            raise RuntimeError('Local source inventory changed during verification; rerun on a fixed tree.')
        after = {str(p.relative_to(ROOT)): digest(p) for p in final_sources + config}
        if before != after:
            raise RuntimeError('Source/configuration changed during verification; rerun on a fixed tree.')
        version = subprocess.check_output([LAKE, 'env', 'lean', '--version'], text=True).strip()
        status.update(verification_status='PASSED', kernel_verification_passed=True,
                      lean_version=version,
                      coverage_status='KERNEL_CHECKED_END_TO_END_PRIMITIVE_PROGRAMS',
                      unconditional_end_to_end_program_certified=True,
                      remaining_obligations=[],
                      local_modules=len(modules), mapped_numbered_statements=len(numbered_labels),
                      mapped_declarations=len(map_names), theorem_declarations=int(summary[1]),
                      all_declarations=int(summary[2]), manuscript_theorem_declarations=int(summary[3]),
                      allowed_axioms=['propext', 'Classical.choice', 'Quot.sound'],
                      audit_negative_controls=f'all {len(fixtures)} rejected',
                      completed_utc=datetime.now(timezone.utc).isoformat(),
                      log_sha256={n: digest(ROOT / n) for n in
                                  ['verification.log', 'axiom-audit.log', 'audit-self-check.log', 'declaration-closure.log', 'dependency-summary.json', 'source-map-check.log']})
        print('PASSED: complete primitive-program endpoints, all local proofs, independent declaration closures, and axiom controls.', flush=True)
    except Exception as exc:
        status.update(verification_status='FAILED', error=str(exc))
        raise
    finally:
        status_path.write_text(json.dumps(status, indent=2) + '\n')
except BaseException as exc:
    failed = json.loads(preflight_status_path.read_text())
    failed.update(verification_status='FAILED', kernel_verification_passed=False,
                  unconditional_end_to_end_program_certified=False, error=str(exc))
    preflight_status_path.write_text(json.dumps(failed, indent=2) + '\n')
    raise
