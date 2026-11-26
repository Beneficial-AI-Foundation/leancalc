#!/usr/bin/env python3
"""Check document routing metadata and the actual bundled icon representations."""
from pathlib import Path
import plistlib
import struct
import zlib

ROOT = Path(__file__).resolve().parent.parent
APP = ROOT/'dist/LeanCalc.app/Contents'

def verify():
    info = plistlib.loads((APP/'Info.plist').read_bytes())
    documents = info['CFBundleDocumentTypes']
    assert {ext for d in documents for ext in d['CFBundleTypeExtensions']} == {'lcalc','csv','ods'}
    assert all(d['LSItemContentTypes'] and d['CFBundleTypeRole'] in ('Editor','Viewer') for d in documents)
    native = info['UTExportedTypeDeclarations'][0]
    assert native['UTTypeIdentifier'] == documents[0]['LSItemContentTypes'][0]
    assert native['UTTypeTagSpecification']['public.filename-extension'] == ['lcalc']
    assert (APP/'Resources/native-startup.tcl').read_bytes() == (ROOT/'lean_calc/mac_documents.tcl').read_bytes()
    icon = (APP/'Resources'/info['CFBundleIconFile']).read_bytes()
    assert icon[:4] == b'icns' and struct.unpack('>I',icon[4:8])[0] == len(icon)
    # Ten required representations: (slot name, pixel size, accepted tags). The 16- and
    # 32-pixel 1x slots accept either PNG (icp4/icp5, written by build_icon's fallback and
    # older iconutil) or Apple's RLE-compressed ARGB (ic04/ic05, written by iconutil on
    # macOS 26). Unrelated chunks such as 'info' are skipped.
    slots = [('16', 16, {b'icp4', b'ic04'}), ('16@2x', 32, {b'ic11'}),
             ('32', 32, {b'icp5', b'ic05'}), ('32@2x', 64, {b'ic12'}),
             ('128', 128, {b'ic07'}), ('128@2x', 256, {b'ic13'}),
             ('256', 256, {b'ic08'}), ('256@2x', 512, {b'ic14'}),
             ('512', 512, {b'ic09'}), ('512@2x', 1024, {b'ic10'})]
    found = []
    pos = 8
    while pos < len(icon):
        assert pos+8 <= len(icon)
        tag, length = struct.unpack('>4sI',icon[pos:pos+8])
        assert length >= 8 and pos+length <= len(icon)
        data = icon[pos+8:pos+length]
        for name, size, tags in slots:
            if tag in tags:
                if data[:8] == b'\x89PNG\r\n\x1a\n':
                    check_png(data, size)
                else:
                    assert tag in (b'ic04', b'ic05'), f'{tag!r} is not a PNG'
                    check_argb(data, size)
                found.append(name)
        pos += length
    assert sorted(found) == sorted(name for name, _, _ in slots), f'icon representations found: {found}'
    print('Bundle verified: three document formats, startup event handler, ten valid icon representations.')

def check_png(png, size):
    assert struct.unpack('>II',png[16:24]) == (size,size)
    offset = 8
    while offset < len(png):
        n = struct.unpack('>I',png[offset:offset+4])[0]
        payload = png[offset+4:offset+8+n]
        assert zlib.crc32(payload) == struct.unpack('>I',png[offset+8+n:offset+12+n])[0]
        offset += n+12

def check_argb(data, size):
    """Apple's 'ARGB' encoding: four channel planes, each byte-run compressed. A control
    byte below 0x80 copies the next n+1 bytes; 0x80 or above repeats the next byte n-125
    times. The data must decode to exactly 4 x size x size bytes with nothing left over."""
    assert data[:4] == b'ARGB'
    decoded, i = 0, 4
    while i < len(data):
        n = data[i]
        if n < 0x80:
            assert i+1+n+1 <= len(data)
            decoded, i = decoded + n+1, i+1+n+1
        else:
            assert i+2 <= len(data)
            decoded, i = decoded + n-125, i+2
    assert decoded == 4*size*size, f'ARGB icon decodes to {decoded} bytes, expected {4*size*size}'
if __name__ == '__main__':
    verify()
