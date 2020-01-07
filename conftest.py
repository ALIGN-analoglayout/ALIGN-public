
import pytest

def pytest_addoption(parser):
    parser.addoption(
        "--runnightly", action="store_true", default=False, help="run slow tests"
    )

def pytest_collection_modifyitems(config, items):
    if config.getoption("--runnightly"):
        # --runnightly given in cli: do not skip nightly tests
        return
    skip_nightly = pytest.mark.skip(reason="need --runnightly option to run")
    for item in items:
        if "nightly" in item.keywords:
            item.add_marker(skip_nightly)
