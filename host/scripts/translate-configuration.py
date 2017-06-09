#!/usr/bin/python

import os
import sys
import json

def load_configuration(path):
	data = {}
	with open(path) as f:
		output = f.read()
	packages=output.split("\n")
	packages = packages[:-1] # remove last line
	for line in packages:
		items = line.split()
		package = items[0]
		features = items[1:]
		data[package] = features
	return data

def save_configuration(filename, configuration):
	with open(filename, 'w') as f:
		json.dump(configuration , f, sort_keys=True, indent=4, separators=(',', ': '))
		f.write('\n')


def load_world(path):
	with open(path) as f:
		output = f.read()
	return { p : {} for p in output.split() }

def save_world(filename, world):
	with open(filename, 'w') as f:
		json.dump(world , f, sort_keys=True, indent=4, separators=(',', ': '))
		f.write('\n')


if __name__ == "__main__":
	if len(sys.argv) != 2:
		print ("usage: ", sys.argv[0], " configuration-path")
		sys.exit(-1)
	path = sys.argv[1]
	outfile = os.path.join(path,"json/configuration.json")
	data = load_configuration(os.path.join(path, "configuration"))
	save_configuration(outfile, data)
	outfile = os.path.join(path,"json/world.json")
	data = load_world(os.path.join(path, "world"))
	save_world(outfile, data)
