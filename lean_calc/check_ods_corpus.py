#!/usr/bin/env python3
"""Verify the pinned real-workbook corpus and record exact import diagnostics."""
import hashlib
import json
from pathlib import Path
import subprocess
ROOT = Path(__file__).resolve().parent.parent
CORPUS = ROOT/'lean_calc/fixtures/ods'

def main():
    manifest = json.loads((CORPUS/'manifest.json').read_text())
    reports = []
    for item in manifest['fixtures']:
        path = CORPUS/item['file']
        before = path.read_bytes()
        assert hashlib.sha256(before).hexdigest() == item['sha256'], item['file']
        result = subprocess.run([str(ROOT/'dist/LeanCalc.app/Contents/MacOS/LeanCalc'),
                                 '--ods-inspect', str(path)], capture_output=True, text=True, timeout=30)
        assert path.read_bytes() == before, 'Importer modified its source'
        assert result.returncode != 0, 'Unsupported fixture unexpectedly imported'
        diagnostic = (result.stderr + result.stdout).strip()
        assert item['diagnostic'] in diagnostic, diagnostic
        reports.append({'file':item['file'], 'sha256':item['sha256'],
                        'source_unchanged':True,'status':'expected rejection',
                        'diagnostic':diagnostic})
    (ROOT/'lean_calc/ods-corpus-results.json').write_text(json.dumps(reports,indent=2)+'\n')
    print('Two pinned Apache OpenOffice fixtures: expected diagnostics; originals unchanged.')
if __name__ == '__main__':
    main()
