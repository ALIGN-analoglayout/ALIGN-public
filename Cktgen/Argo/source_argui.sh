#!/bin/bash
kubectl -n argo port-forward deployment/argo-ui 8001:8001 >& /dev/null &
