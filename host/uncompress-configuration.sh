#!/bin/bash

[ -d configuration/json ] || mkdir -p configuration/json

python scripts/translate-configuration.py configuration
