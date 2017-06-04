#!/usr/bin/python

import os
import os.path
import multiprocessing

md5_cache_path="../portage/usr/portage/metadata/md5-cache"

files = []
for root, dirnames, filenames in os.walk(md5_cache_path):
    files.extend([os.path.join(root, filename) for filename in filenames])


def extract_package(filepath):
	els = filepath.split("/")
	return els[-2] + "/" + els[-1]

multiprocessing.freeze_support()
pool = multiprocessing.Pool(3)

to_find = pool.map(extract_package, files)
lock = multiprocessing.Lock()

def search(filepath):
	global to_find
	global lock
	with open(filepath, 'r') as f:
		s = f.read()
		for el in to_find:
			if el in s:
				with lock:
				 print(filepath + " -> " + el) 

pool.map(search, files)
