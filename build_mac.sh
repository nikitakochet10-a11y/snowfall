#!/bin/bash
# Сборка Snowfall.app на Mac:  bash build_mac.sh
set -e
cd "$(dirname "$0")"
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements-mac.txt
pyinstaller --noconfirm --windowed --name Snowfall \
  --icon Snowfall.icns \
  --osx-bundle-identifier com.snowfall.overlay \
  --hidden-import Quartz --hidden-import AppKit --hidden-import objc --hidden-import ApplicationServices \
  Snowfall.py
# значок только в строке меню, без Dock
/usr/libexec/PlistBuddy -c "Add :LSUIElement bool true" dist/Snowfall.app/Contents/Info.plist 2>/dev/null || true
# подпись «ad hoc», чтобы macOS не ругался на повреждённое приложение
codesign --force --deep --sign - dist/Snowfall.app
cd dist && zip -qry Snowfall-mac.zip Snowfall.app
echo "Готово: dist/Snowfall.app и dist/Snowfall-mac.zip"
