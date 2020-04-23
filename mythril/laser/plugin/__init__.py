""" Laser plugins

This module contains everything to do with laser plugins

Laser plugins are a way of extending laser's functionality without complicating the core business logic.
Different features that have been implemented in the form of plugins are:
- benchmarking
- path pruning

Plugins also provide a way to implement optimisations outside of the mythril code base and to inject them.
The api that laser currently provides is still unstable and will probably change to suit our needs
as more plugins get developed.

For the implementation of plugins the following modules are of interest:
- laser.plugins.plugin
- laser.plugins.signals
- laser.svm

Which show the basic interfaces with which plugins are able to interact
"""
