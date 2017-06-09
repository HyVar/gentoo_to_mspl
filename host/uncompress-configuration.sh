#!/bin/bash

[ -d configuration/json ] || mkdir -p configuration/json

tar xvfj configuration/configuration.tar.bz2 -C configuration
python scripts/translate-configuration.py configuration
mv configuration/profile.json configuration/json
