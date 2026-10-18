#!/usr/bin/env sh
set -eu

mkdir -p docs
coqdoc -t Bonak --no-lib-name --parse-comments --utf8 -d docs \
  -Q _build/default/theories Bonak \
  _build/default/theories/Lib/*.v \
  _build/default/theories/Category/*.v \
  _build/default/theories/Presheaf/*.v \
  _build/default/theories/Equiv/*.v \
  _build/default/theories/SSSet/*.v \
  _build/default/theories/SSGpd/*.v
