#!/usr/bin/env python3
"""Check native tests and compile the LeanCalc manual and conversation record."""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import zipfile

ROOT = Path(__file__).resolve().parent.parent

def escape(text):
    mapping = {'λ': r'$\lambda$', '\\': r'\textbackslash{}', '&': r'\&', '%': r'\%', '$': r'\$', '#': r'\#',
               '_': r'\_', '{': r'\{', '}': r'\}', '~': r'\textasciitilde{}', '^': r'\textasciicircum{}'}
    return ''.join(mapping.get(c, c) for c in text)

def main():
    binary = ROOT/'dist/LeanCalc.app/Contents/MacOS/LeanCalc'
    if any((ROOT/'lean_calc'/name).stat().st_mtime > binary.stat().st_mtime
           for name in ('SparseGrid.lean', 'Features.lean', 'FeatureTests.lean', 'objects.tcl', 'mac_documents.tcl', 'LeanCalcCore.lean', 'MathFunctions.lean', 'Phase2.lean', 'Phase2Tests.lean', 'AdvancedTests.lean', 'Incremental.lean', 'Presentation.lean', 'Stage3Tests.lean', 'OpenDocument.lean', 'InterchangeTests.lean', 'LeanCalc.lean', 'bridge.c', 'interchange.c')):
        raise RuntimeError('Application source changed; run python3 lean_calc/build.py first.')
    result = subprocess.run([str(binary), '--self-test'], check=True, capture_output=True, text=True)
    interactions = subprocess.run([str(binary), '--interaction-self-test'], check=True, capture_output=True, text=True)
    (ROOT/'lean_calc/interaction-test-results.log').write_text(interactions.stdout)
    if '17 interaction checks passed' not in interactions.stdout:
        raise RuntimeError('Expected 17 interaction checks.')
    performance = subprocess.run([str(binary), '--performance-self-test'], check=True, capture_output=True, text=True)
    (ROOT/'lean_calc/performance-test-results.log').write_text(performance.stdout)
    if '12 performance regression checks passed' not in performance.stdout:
        raise RuntimeError('Expected 12 performance regression checks.')
    phase2 = subprocess.run([str(binary), '--phase2-self-test'], check=True, capture_output=True, text=True)
    phase2_ui = subprocess.run([str(binary), '--phase2-interaction-test'], check=True, capture_output=True, text=True)
    (ROOT/'lean_calc/phase2-test-results.log').write_text(phase2.stdout)
    (ROOT/'lean_calc/phase2-interaction-test-results.log').write_text(phase2_ui.stdout)
    if '87 Phase 2 checks passed' not in phase2.stdout or '23 Phase 2 interaction checks passed' not in phase2_ui.stdout:
        raise RuntimeError('Expected 87 Phase 2 core checks and 23 interaction checks.')
    picking = subprocess.run([str(binary), '--formula-picking-test'], check=True, capture_output=True, text=True)
    (ROOT/'lean_calc/formula-picking-test-results.log').write_text(picking.stdout)
    if '25 formula-picking checks passed' not in picking.stdout:
        raise RuntimeError('Expected 25 formula-picking checks.')
    save_tabs = subprocess.run([str(binary), '--save-tabs-test'], check=True, capture_output=True, text=True)
    (ROOT/'lean_calc/save-tabs-test-results.log').write_text(save_tabs.stdout)
    if '19 save-and-tabs checks passed' not in save_tabs.stdout:
        raise RuntimeError('Expected 19 save-and-tabs checks.')
    extra_names = []
    for option, log, expected in [('--math-test', 'math-test-results.log', 82), ('--stage3-test', 'stage3-test-results.log', 30), ('--ods-test', 'ods-test-results.log', 15), ('--stage3-interaction-test', 'stage3-interaction-test-results.log', 8), ('--features-test', 'features-test-results.log', 81), ('--features-interaction-test', 'features-interaction-test-results.log', 13), ('--document-open-test', 'document-open-test-results.log', 17)]:
        extra = subprocess.run([str(binary), option], cwd=ROOT, check=True, capture_output=True, text=True)
        (ROOT/'lean_calc'/log).write_text(extra.stdout)
        passed = [line.removeprefix('PASS: ') for line in extra.stdout.splitlines() if line.startswith('PASS: ')]
        if len(passed) != expected:
            raise RuntimeError(f'{option}: expected {expected} checks, got {len(passed)}')
        extra_names.extend(passed)
    with zipfile.ZipFile(ROOT/'lean_calc/examples/Interoperability.ods') as archive:
        first = archive.infolist()[0]
        if first.filename != 'mimetype' or first.compress_type != 0 or first.extra:
            raise RuntimeError('ODS mimetype must be first, stored and have no extra field.')
        xml = ROOT/'tmp/ods-export-validation.xml'
        xml.parent.mkdir(exist_ok=True)
        xml.write_bytes(archive.read('content.xml'))
    schema_check = subprocess.run(['/usr/bin/xmllint', '--noout', '--relaxng',
                                  str(ROOT/'lean_calc/vendor/odf1.3/schema.rng'), str(xml)],
                                 check=True, capture_output=True, text=True)
    (ROOT/'lean_calc/ods-schema-validation.log').write_text(schema_check.stdout + schema_check.stderr)
    subprocess.run([sys.executable, str(ROOT/'lean_calc/check_ods_corpus.py')], check=True)
    tests = json.loads((ROOT/'lean_calc/tests.json').read_text())
    names = [line.removeprefix('PASS: ') for line in result.stdout.splitlines() if line.startswith('PASS: ')]
    if len(names) != 61 or names != [t['description'] for t in tests]:
        raise RuntimeError('Native results and 61-test documentation catalogue differ.')
    (ROOT/'lean_calc/native-test-results.log').write_text(result.stdout)
    catalogue = ''.join(f"{t['id']:02d} & {escape(t['description'])}.\\\\\n" for t in tests)
    tex = ROOT/'LeanCalc.tex'
    source = tex.read_text()
    start, rest = source.split('% BEGIN TEST CATALOGUE\n', 1)
    _, end = rest.split('% END TEST CATALOGUE', 1)
    source = start + '% BEGIN TEST CATALOGUE\n' + catalogue + '% END TEST CATALOGUE' + end
    phase2_names = [line.removeprefix('PASS: ') for line in (phase2.stdout + phase2_ui.stdout).splitlines() if line.startswith('PASS: ')]
    if '% BEGIN PHASE2 CATALOGUE\n' in source:
        start, rest = source.split('% BEGIN PHASE2 CATALOGUE\n', 1)
        _, end = rest.split('% END PHASE2 CATALOGUE', 1)
        catalogue = ''.join(f"{i:02d} & {escape(name)}.\\\\\n" for i, name in enumerate(phase2_names, 1))
        source = start + '% BEGIN PHASE2 CATALOGUE\n' + catalogue + '% END PHASE2 CATALOGUE' + end
    if '% BEGIN PICKING CATALOGUE\n' in source:
        start, rest = source.split('% BEGIN PICKING CATALOGUE\n', 1)
        _, end = rest.split('% END PICKING CATALOGUE', 1)
        names = [line.removeprefix('PASS: ') for line in picking.stdout.splitlines() if line.startswith('PASS: ')]
        catalogue = ''.join(f"{i:02d} & {escape(name)}.\\\\\n" for i, name in enumerate(names, 1))
        source = start + '% BEGIN PICKING CATALOGUE\n' + catalogue + '% END PICKING CATALOGUE' + end
    if '% BEGIN SAVE TABS CATALOGUE\n' in source:
        start, rest = source.split('% BEGIN SAVE TABS CATALOGUE\n', 1)
        _, end = rest.split('% END SAVE TABS CATALOGUE', 1)
        names = [line.removeprefix('PASS: ') for line in save_tabs.stdout.splitlines() if line.startswith('PASS: ')]
        catalogue = ''.join(f"{i:02d} & {escape(name)}.\\\\\n" for i, name in enumerate(names, 1))
        source = start + '% BEGIN SAVE TABS CATALOGUE\n' + catalogue + '% END SAVE TABS CATALOGUE' + end
    if '% BEGIN ADVANCED CATALOGUE\n' in source:
        start, rest = source.split('% BEGIN ADVANCED CATALOGUE\n', 1)
        _, end = rest.split('% END ADVANCED CATALOGUE', 1)
        catalogue = ''.join(f"{i:02d} & {escape(name)}.\\\\\n" for i, name in enumerate(extra_names, 1))
        source = start + '% BEGIN ADVANCED CATALOGUE\n' + catalogue + '% END ADVANCED CATALOGUE' + end
    tex.write_text(source)
    out = ROOT/'tmp/pdfs/leancalc-latex'
    out.mkdir(parents=True, exist_ok=True)
    subprocess.run([shutil.which('latexmk') or '/Library/TeX/texbin/latexmk', '-pdf',
                    '-interaction=nonstopmode', '-halt-on-error', '-file-line-error',
                    '-outdir='+str(out), 'LeanCalc.tex'], cwd=ROOT, check=True)
    shutil.copy2(out/'LeanCalc.pdf', ROOT/'LeanCalc.pdf')
    print('Compiled:', ROOT/'LeanCalc.pdf')
    if (ROOT/'answers.tex').is_file():
        subprocess.run([sys.executable, str(ROOT/'build_answers.py')], cwd=ROOT, check=True)

if __name__ == '__main__':
    main()
