!#/bin/bash

pushd $ALIGN_WORK_DIR
make DESIGN=switched_capacitor_filter
popd

for nm in telescopic_ota switched_capacitor_combination switched_capacitor_filter; do
    cp $ALIGN_WORK_DIR/switched_capacitor_filter/pnr_output/Results/${nm}_0.db.json $ALIGN_HOME/PlaceRouteHierFlow/PnRPython/tests/${nm}-freeze.json
done

pushd $ALIGN_HOME/PlaceRouteHierFlow/PnRPython/
pytest --capture=no > LOG
popd
