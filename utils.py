#!/usr/bin/python


"""
utils.py: this file contains utility functions and classes for translating the gentoo's ebuild in well-formed Dependent SPL and processing them
"""

__author__ = "Jacopo Mauro"
__copyright__ = "Copyright 2017, Jacopo Mauro"
__license__ = "ISC"
__version__ = "0.1"
__maintainer__ = "Jacopo Mauro"
__email__ = "mauro.jacopo@gmail.com"
__status__ = "Prototype"

import logging
import settings
import re

import networkx


def preprocess(mspl,initial_configuration):
    # crate graph with no loops
    graph = create_graph(mspl,initial_configuration)
    # add information about descendants
    reachability_analysis(graph,mspl)


class Node:
    def __init__(self, name):
        self.names = set([name])

    def add_names(self,names):
        self.names.update(names)

def merge_nodes(graph,nodes):

    in_edges = set([x for x,y in graph.in_edges(nodes)])
    out_edges = set([x for y,x in graph.out_edges(nodes)])

    names = set()
    for i in nodes:
        names.update(i.names)
    #     in_edges.update(set([x for x,_ in graph.in_edges(i)]))
    #     out_edges.update(set([x for _,x in graph.out_edges(i)]))
    in_edges.difference_update(nodes)
    out_edges.difference_update(nodes)
    node = Node(nodes[0].names.pop())
    node.add_names(names)
    graph.add_node(node)
    # logging.debug("Merging nodes: " + unicode(names))
    if in_edges:
        for i in in_edges:
            graph.add_edge(i,node)
    if out_edges:
        for i in list(out_edges):
            graph.add_edge(node,i)
    graph.remove_nodes_from(nodes)


def create_graph(mspl,initial_configuration):
    graph = networkx.DiGraph()

    added = {}
    to_process = set()

    # add root node
    name = settings.ROOT_SPL_NAME
    node = Node(name)
    graph.add_node(node)
    to_process.add(name)
    added[name] = node

    # add nodes for the intial configuration that are installed
    for i in initial_configuration.keys():
        name = re.sub(settings.VERSION_RE,"",i)
        if name in mspl:
            node = Node(name)
            graph.add_node(node)
            to_process.add(name)
            added[name] = node
        else:
            logging.warning("The information about the installed package " + i + "(" + name + ") can not be found." +
                            "This package will be ignored.")

    # add edges and nodes (only base packages, not versions)
    while to_process:
        u_name = to_process.pop()
        for i in mspl[u_name]['configures']:
            v_name = re.sub(settings.VERSION_RE, "", i)
            if v_name in mspl:
                if i not in added:
                    if v_name not in added:
                        node = Node(v_name)
                        graph.add_node(node)
                        added[v_name] = node
                        to_process.add(v_name)
                    added[i] = added[v_name]
                    to_process.add(i)
                if not u_name.startswith(v_name):
                    graph.add_edge(added[u_name], added[i])
            else:
                logging.warning("The package " + u_name + " requires the configuration of package " + i +
                                " which is not found. Skipping this dependency.")

    logging.debug("Graph created with " + unicode(len(graph.nodes())) + " nodes and " +
                  unicode(len(graph.edges())) + " edges")

    # merge loops, if any
    try:
        cycle = networkx.find_cycle(graph, orientation='original')
    except networkx.exception.NetworkXNoCycle:
        cycle = []
    while cycle:
        logging.debug("Find cycle of length " + unicode(len(cycle)))
        merge_nodes(graph,[x for x,_ in cycle])
        logging.debug("Graph has " + unicode(len(graph.nodes())) + " nodes and " +
                      unicode(len(graph.edges())) + " edges")
        try:
            cycle = networkx.find_cycle(graph, orientation='original')
        except networkx.exception.NetworkXNoCycle:
            cycle = []

    logging.debug("Final graph has " + unicode(len(graph.nodes())) + " nodes and " +
                  unicode(len(graph.edges())) + " edges")

    return graph


def reachability_analysis(graph,mspl):
    for i in graph.nodes():
        nodes = networkx.descendants(graph,i)

        pkgs = []
        for j in nodes:
            pkgs.extend(list(j.names))
        for j in i.names:
            mspl[j]["include"] = pkgs

