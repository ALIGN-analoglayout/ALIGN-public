import pytest
from align.utils import logmanager
logmanager.reconfigure_loglevels(console_level='WARNING')


def pytest_addoption(parser):
    parser.addoption(
        "--runnightly", action="store_true", default=False, help="run nightly tests"
    )
    parser.addoption(
        "--runregression", action="store_true", default=False, help="run regression tests"
    )
    parser.addoption(
        "--maxerrors", type=int, help="Maximum number of circuit errors to tolerate (Use with --runnightly)", default=0
    )
    parser.addoption(
        "--router_mode", type=str, help="Router mode for nightly run (Use with --runnightly)", default='top_down'
    )
    parser.addoption(
        "--skipGDS", action="store_true", default=False, help="Skip GDS for nightly run (Use with --runnightly)"
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


def pytest_generate_tests(metafunc):
    if "maxerrors" in metafunc.fixturenames:
        maxerrors = metafunc.config.getoption("--maxerrors")
        metafunc.parametrize("maxerrors", [maxerrors])
    if "router_mode" in metafunc.fixturenames:
        router_mode = metafunc.config.getoption("--router_mode")
        metafunc.parametrize("router_mode", [router_mode])
    if "skipGDS" in metafunc.fixturenames:
        metafunc.parametrize("skipGDS", [True])

