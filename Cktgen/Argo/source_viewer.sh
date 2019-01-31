#!/bin/bash

argo submit route_artifacts.argo --entrypoint view-artifacts --name view-artifacts
sleep 10
kubectl port-forward view-artifacts 8002:8000 >& /dev/null &

