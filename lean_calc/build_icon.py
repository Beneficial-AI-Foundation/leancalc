#!/usr/bin/env python3
"""Package the selected, unchanged artwork into standard macOS icon sizes."""
from pathlib import Path
import subprocess
import struct

ROOT = Path(__file__).resolve().parent.parent

def build_icon(destination):
    source = ROOT / 'lean_calc/assets/LeanCalc.png'
    iconset = ROOT / '.lean-calc-build/LeanCalc.iconset'
    iconset.mkdir(parents=True, exist_ok=True)
    for points in (16, 32, 128, 256, 512):
        for scale in (1, 2):
            pixels = points * scale
            name = f'icon_{points}x{points}' + ('@2x' if scale == 2 else '') + '.png'
            subprocess.run(['/usr/bin/sips', '-z', str(pixels), str(pixels), str(source),
                            '--out', str(iconset / name)], check=True, capture_output=True)
    result = subprocess.run(['/usr/bin/iconutil', '-c', 'icns', str(iconset), '-o', str(destination)], capture_output=True)
    if result.returncode == 0:
        return
    # Same standard PNG-based ICNS packaging used for the sibling LeanWord app.
    # Some managed macOS installations cannot use iconutil's encoder.
    representations = [
        (b'icp4', 'icon_16x16.png'), (b'ic11', 'icon_16x16@2x.png'),
        (b'icp5', 'icon_32x32.png'), (b'ic12', 'icon_32x32@2x.png'),
        (b'ic07', 'icon_128x128.png'), (b'ic13', 'icon_128x128@2x.png'),
        (b'ic08', 'icon_256x256.png'), (b'ic14', 'icon_256x256@2x.png'),
        (b'ic09', 'icon_512x512.png'), (b'ic10', 'icon_512x512@2x.png'),
    ]
    chunks = []
    for kind, filename in representations:
        data = (iconset / filename).read_bytes()
        if data[:8] != b'\x89PNG\r\n\x1a\n':
            raise ValueError('Invalid icon representation: ' + filename)
        chunks.append(kind + struct.pack('>I', len(data) + 8) + data)
    payload = b''.join(chunks)
    Path(destination).write_bytes(b'icns' + struct.pack('>I', len(payload) + 8) + payload)
