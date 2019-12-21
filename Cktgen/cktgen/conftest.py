# content of conftest.py

import pytest


def pytest_addoption(parser):
    parser.addoption(
        "--run_intel_22nm", action="store_true", default=False, help="run intel_22nm tests"
    )


def pytest_configure(config):
    config.addinivalue_line("markers", "intel_22nm: mark test that needs protected process parameters (intel_22nm)")


def pytest_collection_modifyitems(config, items):
    if config.getoption("--run_intel_22nm"):
        return
    for item in items:
        if "intel_22nm" in item.keywords:
            item.add_marker(pytest.mark.skip(reason="need --run_intel_22nm option to run"))
