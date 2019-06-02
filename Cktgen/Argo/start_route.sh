#!/bin/bash
argo delete route
argo submit --watch route.argo --name route -p show-metal-templates=""
