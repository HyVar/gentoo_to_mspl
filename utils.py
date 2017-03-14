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


def preprocess(mspl,initial_configuration,package_request):
    # crate graph with no loops
    graph = create_graph(mspl,initial_configuration,package_request)
    # add information about descendants
    reachability_analysis(graph,mspl)


class Node:
    def __init__(self, name):
        self.names = set([name])

    def add_names(self,names):
        self.names.update(names)

def merge_nodes(graph,nodes):

    in_edges = set()
    out_edges = set()

    for x in graph.in_edges(nodes):
        if x[0] not in nodes:
            in_edges.update([x[0]])
        #     logging.debug("Removing edge " + unicode((x[0].names,x[1].names)))
        # else:
        #     logging.debug("Removing self edge " + unicode((x[0].names, x[1].names)))
        graph.remove_edge(*x)

    for x in graph.out_edges(nodes):
        if x[1] not in nodes:
            out_edges.update([x[1]])
        #     logging.debug("Removing edge " + unicode((x[0].names, x[1].names)))
        # else:
        #     logging.debug("Removing self edge " + unicode((x[0].names, x[1].names)))
        graph.remove_edge(*x)

    names = set()
    for i in nodes:
        names.update(i.names)
        graph.remove_node(i)

    node = Node(names.pop())
    node.add_names(names)
    graph.add_node(node)

    if in_edges:
        for i in in_edges:
            graph.add_edge(i,node)
            # logging.debug("Creating edge " + unicode((i.names, node.names)))
    if out_edges:
        for i in out_edges:
            graph.add_edge(node,i)
            # logging.debug("Creating edge " + unicode((node.names, i.names)))
    return node


def create_graph(mspl,initial_configuration,package_request):
    graph = networkx.DiGraph()

    added = {}
    to_process = set()

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

    # add root node dependencies
    for i in package_request:
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

    logging.debug("Graph created with " + unicode(graph.number_of_nodes()) + " nodes and " +
                  unicode(graph.size()) + " edges")

    # merge loops, if any
    # use simple_cycles to start procedure (find_cycle seems to have a bug and does not find all the cycles)
    cycle = next(networkx.simple_cycles(graph),[])
    while cycle:
        logging.debug("Find cycle of length " + unicode(len(cycle)))
        # logging.debug(unicode([ (x[0].names,x[1].names) for x in cycle]))
        node = merge_nodes(graph,cycle)
        logging.debug("Graph has " + unicode(graph.number_of_nodes()) + " nodes and " +
                      unicode(graph.size()) + " edges")
        try:
            cycle = [ x[0] for x in networkx.find_cycle(graph,source=node,orientation='original')]
        except networkx.exception.NetworkXNoCycle:
            cycle = []
        while cycle:
            logging.debug("Find cycle of length " + unicode(len(cycle)))
            node = merge_nodes(graph, cycle)
            logging.debug("Graph has " + unicode(graph.number_of_nodes()) + " nodes and " +
                          unicode(graph.size()) + " edges")
            try:
                cycle = [x[0] for x in networkx.find_cycle(graph,source=node,orientation='original')]
            except networkx.exception.NetworkXNoCycle:
                cycle = []
        # to make sure every cycle has been captured
        cycle = next(networkx.simple_cycles(graph), [])

    logging.debug("Final graph has " + unicode(graph.number_of_nodes()) + " nodes and " +
                  unicode(graph.size()) + " edges")

    return graph


def reachability_analysis(graph,mspl):
    for i in graph.nodes():
        nodes = networkx.descendants(graph,i)

        pkgs = []
        for j in nodes:
            pkgs.extend(list(j.names))
        for j in i.names:
            mspl[j]["descendants"] = pkgs
            mspl[j]["loop"] = list(i.names)

