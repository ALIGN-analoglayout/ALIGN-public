import pytest

def pytest_addoption(parser):
    parser.addoption(
        "--runnightly", action="store_true", default=False, help="run nightly tests"
    )
    parser.addoption(
        "--runregression", action="store_true", default=False, help="run regression tests"
    )

def pytest_collection_modifyitems(config, items):
    if not config.getoption("--runnightly"):
        skip_nightly = pytest.mark.skip(reason="need --runnightly option to run")
        for item in items:
            if "nightly" in item.keywords:
                item.add_marker(skip_nightly)
    if not config.getoption("--runregression"):
        skip_regression = pytest.mark.skip(reason="need --runregression option to run")
        for item in items:
            if "regression" in item.keywords:
                item.add_marker(skip_regression)
