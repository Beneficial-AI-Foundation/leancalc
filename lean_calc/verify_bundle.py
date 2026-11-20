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
    expected = {b'icp4':16,b'ic11':32,b'icp5':32,b'ic12':64,b'ic07':128,
                b'ic13':256,b'ic08':256,b'ic14':512,b'ic09':512,b'ic10':1024}
    found = set()
    pos = 8
    while pos < len(icon):
        tag, length = struct.unpack('>4sI',icon[pos:pos+8])
        assert length >= 8 and pos+length <= len(icon)
        png = icon[pos+8:pos+length]
        if tag in expected:
            assert png[:8] == b'\x89PNG\r\n\x1a\n'
            assert struct.unpack('>II',png[16:24]) == (expected[tag],expected[tag])
            offset = 8
            while offset < len(png):
                n = struct.unpack('>I',png[offset:offset+4])[0]
                payload = png[offset+4:offset+8+n]
                assert zlib.crc32(payload) == struct.unpack('>I',png[offset+8+n:offset+12+n])[0]
                offset += n+12
            found.add(tag)
        pos += length
    assert found == set(expected), found
    print('Bundle verified: three document formats, startup event handler, ten valid icon representations.')
if __name__ == '__main__':
    verify()
