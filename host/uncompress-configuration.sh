#!/bin/bash

[ -d configuration/json ] || mkdir configuration/json

gunzip -c configuration/world.gz > configuration/json/world
python scripts/translate-configuration.py configuration/configuration.gz
