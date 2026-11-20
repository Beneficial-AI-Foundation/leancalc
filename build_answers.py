#!/usr/bin/env python3
"""Compile the user-facing conversation record without replacing its contents."""
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent


def main():
    out = ROOT / 'tmp/pdfs/answers-latex'
    out.mkdir(parents=True, exist_ok=True)
    subprocess.run([
        shutil.which('latexmk') or '/Library/TeX/texbin/latexmk',
        '-pdf', '-interaction=nonstopmode', '-halt-on-error', '-file-line-error',
        '-outdir=' + str(out), 'answers.tex',
    ], cwd=ROOT, check=True)
    shutil.copy2(out / 'answers.pdf', ROOT / 'answers.pdf')
    print('Compiled:', ROOT / 'answers.pdf')


if __name__ == '__main__':
    main()
