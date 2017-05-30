#!/bin/bash

REQUEST_FILE=$1
ENV=$2

# e.g., ENV=amd64

python scripts/portage2hyvarrec/reconfigure.py -v portage/json/hyvarrec $REQUEST_FILE configuration/json/configuration.json configuration/json/new_configuration.json configuration/package.use configuration/update.sh $ENV

