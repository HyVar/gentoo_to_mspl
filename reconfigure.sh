#!/bin/bash

REQUEST_FILE=$1
ENV=$2

# e.g., ENV=amd64

python host/scripts/portage2hyvarrec/reconfigure.py -v host/portage/json/hyvarrec $REQUEST_FILE host/configuration/json/configuration.json host/configuration/json/new_configuration.json host/configuration/package.use configuration/update.sh $ENV

