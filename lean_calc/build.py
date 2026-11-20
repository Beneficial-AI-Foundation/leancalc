#!/usr/bin/env python3
"""Compile Lean -> C -> native macOS app; Python is only a build tool."""
import argparse
import json
import os
from pathlib import Path
import plistlib
import shutil
import subprocess
import sys
from build_icon import build_icon

ROOT = Path(__file__).resolve().parent.parent
SOURCE = ROOT / 'lean_calc'
BUILD = ROOT / '.lean-calc-build'
APP = ROOT / 'dist/LeanCalc.app'
VERSION = 'leanprover--lean4---v4.35.0-rc3'


def run(*args):
    print('+', ' '.join(map(str, args)), flush=True)
    subprocess.run(list(map(str, args)), cwd=ROOT, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--toolchain', type=Path, default=Path.home() / '.elan/toolchains' / VERSION)
    parser.add_argument('--tk-bundle', type=Path, default=ROOT / 'vendor/tcltk-9.0.4')
    parser.add_argument('--gui-test', action='store_true')
    options = parser.parse_args()
    toolchain = options.toolchain.resolve()
    runtime = options.tk_bundle.resolve()
    if not (toolchain / 'bin/lean').exists():
        parser.error('Install Lean 4.35.0-rc3 or supply --toolchain.')
    if not (runtime / 'libtcl9.0.dylib').exists():
        parser.error('Supply --tk-bundle with Tcl/Tk 9.0.4 libraries and _tcl_data/_tk_data.')
    BUILD.mkdir(exist_ok=True)
    generated = SOURCE / 'generated'
    generated.mkdir(exist_ok=True)
    os.environ['LEAN_PATH'] = str(SOURCE)
    # Keep the Tcl source and its compiled Lean literal synchronized.
    ui_source = SOURCE / 'LeanCalc.lean'
    ui_text = ui_source.read_text()
    lines = ui_text.splitlines()
    literal = 'def objectUIScript : String := ' + json.dumps((SOURCE / 'objects.tcl').read_text(), ensure_ascii=False)
    lines = [literal if line.startswith('def objectUIScript : String := ') else line for line in lines]
    updated_ui = '\n'.join(lines) + '\n'
    if updated_ui != ui_text:
        ui_source.write_text(updated_ui)
    for module in ('SparseGrid', 'LeanCalcCore', 'MathFunctions', 'Phase2', 'Phase2Tests', 'AdvancedTests', 'Incremental', 'Features', 'Presentation', 'Stage3Tests', 'OpenDocument', 'InterchangeTests', 'FeatureTests', 'LeanCalc'):
        run(toolchain / 'bin/lean', '-R', SOURCE, '-o', SOURCE / (module + '.olean'), '-c', generated / (module + '.c'), SOURCE / (module + '.lean'))
    # Only replace our own build artifact after successful Lean compilation.
    if APP.exists():
        shutil.rmtree(APP)
    contents = APP / 'Contents'
    binaries = contents / 'MacOS'
    libraries = contents / 'Frameworks'
    resources = contents / 'Resources'
    for folder in (binaries, libraries, resources):
        folder.mkdir(parents=True, exist_ok=True)
    for name in ('libtcl9.0.dylib', 'libtcl9tk9.0.dylib'):
        shutil.copy2(runtime / name, libraries / name)
    for src, dst in (('_tcl_data', 'tcl9.0'), ('_tk_data', 'tk9.0'), ('tcl9', 'tcl9')):
        shutil.copytree(runtime / src, resources / dst, symlinks=False)
    shutil.copy2(SOURCE / 'mac_documents.tcl', resources / 'native-startup.tcl')
    os.environ['LEAN_CC'] = '/usr/bin/clang'
    os.environ['MACOSX_DEPLOYMENT_TARGET'] = '14.0'
    # Use macOS 14-compatible static GMP/libuv; the toolchain copies target macOS 15.
    compat = BUILD / 'compat-libs'
    compat.mkdir(exist_ok=True)
    for name in ('libgmp.a', 'libuv.a'):
        dependency = Path('/opt/homebrew/lib') / name
        if not dependency.exists():
            parser.error('Install Homebrew gmp and libuv (static libraries required).')
        if (compat / name).exists():
            (compat / name).unlink()
        shutil.copy2(dependency, compat / name)
    sdk = subprocess.check_output(['/usr/bin/xcrun', '--show-sdk-path'], text=True).strip()
    run(toolchain / 'bin/leanc', '-O2', '-isysroot', sdk, '-I', SOURCE / 'vendor/tcl9.0.4', '-o', binaries / 'LeanCalc',
        generated / 'SparseGrid.c', generated / 'LeanCalcCore.c', generated / 'MathFunctions.c', generated / 'Phase2.c', generated / 'Phase2Tests.c', generated / 'AdvancedTests.c', generated / 'Incremental.c', generated / 'Features.c', generated / 'Presentation.c', generated / 'Stage3Tests.c', generated / 'OpenDocument.c', generated / 'InterchangeTests.c', generated / 'FeatureTests.c', generated / 'LeanCalc.c', SOURCE / 'bridge.c', SOURCE / 'interchange.c', '-I', Path(sdk) / 'usr/include/libxml2', '-I', SOURCE / 'vendor/libarchive', '-lxml2', '-larchive.2', '-L', compat, '-L', toolchain / 'lib', '-L', libraries, '-ltcl9.0', '-ltcl9tk9.0',
        '-Wl,-rpath,@executable_path/../Frameworks')
    build_icon(resources / 'LeanCalc.icns')
    info = {
        'CFBundleExecutable': 'LeanCalc', 'CFBundleName': 'LeanCalc',
        'CFBundleDisplayName': 'LeanCalc', 'CFBundleIdentifier': 'local.productivity.LeanCalc',
        'CFBundleInfoDictionaryVersion': '6.0',
        'CFBundlePackageType': 'APPL', 'CFBundleShortVersionString': '0.5.1', 'CFBundleVersion': '11',
        'CFBundleIconFile': 'LeanCalc.icns', 'LSMinimumSystemVersion': '14.0',
        'NSHighResolutionCapable': True,
        'CFBundleDocumentTypes': [
            {'CFBundleTypeName': 'LeanCalc workbook', 'CFBundleTypeRole': 'Editor',
             'LSHandlerRank': 'Owner', 'LSItemContentTypes': ['local.productivity.leancalc.workbook'],
             'CFBundleTypeExtensions': ['lcalc'], 'CFBundleTypeIconFile': 'LeanCalc.icns'},
            {'CFBundleTypeName': 'CSV spreadsheet', 'CFBundleTypeRole': 'Viewer',
             'LSHandlerRank': 'Alternate', 'LSItemContentTypes': ['public.comma-separated-values'],
             'CFBundleTypeExtensions': ['csv']},
            {'CFBundleTypeName': 'OpenDocument spreadsheet', 'CFBundleTypeRole': 'Viewer',
             'LSHandlerRank': 'Alternate', 'LSItemContentTypes': ['org.oasis-open.opendocument.spreadsheet'],
             'CFBundleTypeExtensions': ['ods']},
        ],
        'UTExportedTypeDeclarations': [{
            'UTTypeIdentifier': 'local.productivity.leancalc.workbook',
            'UTTypeDescription': 'LeanCalc workbook',
            'UTTypeConformsTo': ['public.json'],
            'UTTypeTagSpecification': {'public.filename-extension': ['lcalc']},
        }],
        'UTImportedTypeDeclarations': [{
            'UTTypeIdentifier': 'org.oasis-open.opendocument.spreadsheet',
            'UTTypeDescription': 'OpenDocument spreadsheet',
            'UTTypeConformsTo': ['public.data'],
            'UTTypeTagSpecification': {'public.filename-extension': ['ods'],
                                       'public.mime-type': 'application/vnd.oasis.opendocument.spreadsheet'},
        }],

    }
    with (contents / 'Info.plist').open('wb') as stream:
        plistlib.dump(info, stream)
    licenses = resources / 'Licenses'
    licenses.mkdir()
    shutil.copy2(toolchain / 'LICENSE', licenses / 'Lean-LICENSE')
    shutil.copy2(toolchain / 'LICENSES', licenses / 'Lean-dependencies.txt')
    for package, names in [('gmp', ['COPYING', 'COPYING.LESSERv3']), ('libuv', ['LICENSE', 'LICENSE-extra'])]:
        package_root = (Path('/opt/homebrew/opt') / package).resolve()
        for name in names:
            shutil.copy2(package_root / name, licenses / (package + '-' + name))
    for name in ('Tcl-license.terms', 'Tk-license.terms', 'Libarchive-COPYING'):
        shutil.copy2(SOURCE / 'vendor' / name, licenses / name)
    run(sys.executable, SOURCE / 'verify_bundle.py')
    run(binaries / 'LeanCalc', '--self-test')
    if options.gui_test:
        run(binaries / 'LeanCalc', '--gui-self-test')
    run(sys.executable, SOURCE / 'build_document.py')
    shutil.copy2(ROOT / 'LeanCalc.pdf', resources / 'LeanCalc.pdf')
    for library in libraries.glob('*.dylib'):
        run('/usr/bin/codesign', '--force', '--sign', '-', library)
    run('/usr/bin/codesign', '--force', '--sign', '-', APP)
    run('/usr/bin/codesign', '--verify', '--deep', '--strict', APP)
    zip_path = ROOT / 'dist/LeanCalc-AppleSilicon.zip'
    if zip_path.exists():
        zip_path.unlink()
    run('/usr/bin/ditto', '-c', '-k', '--sequesterRsrc', '--keepParent', APP, zip_path)
    diagnostic = ROOT / 'dist/Diagnose LeanCalc.command'
    shutil.copy2(SOURCE / 'Diagnose LeanCalc.command', diagnostic)
    diagnostic.chmod(0o755)
    print('Diagnostic launcher:', diagnostic)
    print('Built:', APP)
    print('Generated C:', generated / 'LeanCalc.c')

if __name__ == '__main__':
    main()
