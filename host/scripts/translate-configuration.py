#!/usr/bin/python

import os
import sys
import gzip
import json

def load_configuration(path):
	data = {}
	f = gzip.open(path)
	output = f.read()
	f.close()
	packages=output.split("\n")
	packages = packages[:-1] # remove last line
	for line in packages:
		items = line.split()
		package = items[0]
		features = items[1:]
		data[package] = features
	return data

def save_configuration(filename, configuration):
	f = open(filename, 'w')
	json.dump(configuration , f, sort_keys=True, indent=4, separators=(',', ': '))
	f.write('\n')
	f.close()


if __name__ == "__main__":
	if len(sys.argv) != 2:
		print ("usage: ", sys.argv[0], " configuration.gz")
		sys.exit(-1)
	path = sys.argv[1]
	outfile = os.path.join(os.path.dirname(path),"json/configuration")
	data = load_configuration(path)
	save_configuration(outfile, data)
