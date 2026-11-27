#!/usr/bin/env python3
"""Build static GMP and libuv for macOS 14, so LeanCalc really runs on macOS 14+.

Homebrew's static libraries target the macOS they were built for (GMP 15.0,
libuv 26.0 on a current Mac), which would raise the app's minimum macOS. This
downloads pinned sources, checks their SHA-256, and builds both libraries with
MACOSX_DEPLOYMENT_TARGET=14.0 into .lean-calc-build/compat-libs-14, which
build.py then uses automatically.
"""
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import tarfile
import urllib.request

ROOT = Path(__file__).resolve().parent.parent
WORK = ROOT / '.lean-calc-build/compat-src'
OUT = ROOT / '.lean-calc-build/compat-libs-14'
TARGET = '14.0'
SOURCES = {
    'gmp': ('https://ftp.gnu.org/gnu/gmp/gmp-6.3.0.tar.xz',
            'a3c2b80201b89e68616f4ad30bc66aee4927c3ce50e33929ca819d5c43538898'),
    'libuv': ('https://dist.libuv.org/dist/v1.53.0/libuv-v1.53.0.tar.gz',
              'cb0d6dd2128d5a95bd242c6cc982a24fe608fa93da57b6b4ec763b0018c53e64'),
}


def run(*args, cwd):
    print('+', ' '.join(map(str, args)), flush=True)
    subprocess.run(list(map(str, args)), cwd=cwd, check=True)


def fetch(name):
    url, digest = SOURCES[name]
    archive = WORK / url.rsplit('/', 1)[1]
    if not archive.exists():
        print('Downloading', url, flush=True)
        with urllib.request.urlopen(url) as response:
            archive.write_bytes(response.read())
    if hashlib.sha256(archive.read_bytes()).hexdigest() != digest:
        archive.unlink()
        raise SystemExit(f'{archive.name}: SHA-256 mismatch; download removed.')
    folder = WORK / name
    if folder.exists():
        shutil.rmtree(folder)
    folder.mkdir()
    with tarfile.open(archive) as tar:
        tar.extractall(folder, filter='data')
    return next(folder.iterdir())


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    OUT.mkdir(parents=True, exist_ok=True)
    os.environ['MACOSX_DEPLOYMENT_TARGET'] = TARGET
    flags = f'-O2 -arch arm64 -mmacosx-version-min={TARGET}'
    gmp = fetch('gmp')
    run('./configure', '--enable-static', '--disable-shared', '--with-pic',
        '--host=aarch64-apple-darwin', f'--prefix={WORK / "gmp-install"}',
        'CC=/usr/bin/clang', f'CFLAGS={flags}', cwd=gmp)
    run('make', f'-j{os.cpu_count()}', cwd=gmp)
    run('make', 'install', cwd=gmp)
    shutil.copy2(WORK / 'gmp-install/lib/libgmp.a', OUT / 'libgmp.a')
    uv = fetch('libuv')
    cmake = shutil.which('cmake') or '/opt/homebrew/bin/cmake'
    run(cmake, '-S', uv, '-B', uv / 'build', '-DCMAKE_BUILD_TYPE=Release',
        '-DLIBUV_BUILD_SHARED=OFF', '-DLIBUV_BUILD_TESTS=OFF', '-DCMAKE_OSX_ARCHITECTURES=arm64',
        f'-DCMAKE_OSX_DEPLOYMENT_TARGET={TARGET}', cwd=WORK)
    run(cmake, '--build', uv / 'build', '--parallel', cwd=WORK)
    shutil.copy2(uv / 'build/libuv.a', OUT / 'libuv.a')
    print('Built macOS', TARGET, 'static libraries in', OUT)


if __name__ == '__main__':
    main()
