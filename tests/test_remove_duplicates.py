from fabric_14nm_mock.removeDuplicates import *

def test_vertical():
    terminals = [{'layer': 'metal1', 'netName': 'x', 'rect': [0, 0, 100, 300]}]
    data = {"bbox": [0, 100, 0, 100], "terminals": terminals,
            "globalRoutes": [], "globalRouteGrid": []}
    removeDuplicates(data)


def test_horizontal():
    terminals = [{'layer': 'metal2', 'netName': 'x', 'rect': [0, 0, 300, 100]}]
    data = {"bbox": [0, 100, 0, 100], "terminals": terminals,
            "globalRoutes": [], "globalRouteGrid": []}
    removeDuplicates(data)


def test_different_widths():
    terminals = [{'layer': 'metal2', 'netName': 'x', 'rect': [0, -50, 300, 50]},
                 {'layer': 'metal2', 'netName': 'x', 'rect': [0, -60, 300, 60]}]
    data = {"bbox": [0, 100, 0, 100], "terminals": terminals,
            "globalRoutes": [], "globalRouteGrid": []}
    with pytest.raises(AssertionError):
        removeDuplicates(data)


def test_bad_layer():
    terminals = [{'layer': 'metal14',
                  'netName': 'x', 'rect': [0, -50, 300, 50]}]
    data = {"bbox": [0, 100, 0, 100], "terminals": terminals,
            "globalRoutes": [], "globalRouteGrid": []}
    with pytest.raises(AssertionError):
        removeDuplicates(data)


def test_overlapping():
    terminals = [{'layer': 'metal2', 'netName': 'x', 'rect': [0, -50, 300, 50]},
                 {'layer': 'metal2', 'netName': 'x', 'rect': [200, -50, 600, 50]}]
    data = {"bbox": [0, -50, 600, 50], "terminals": terminals,
            "globalRoutes": [], "globalRouteGrid": []}
    newData = removeDuplicates(data)
    assert len(newData['terminals']) == 1
    assert newData['terminals'][0]['rect'] == [0, -50, 600, 50]


def test_short():
    terminals = [{'layer': 'metal2', 'netName': 'x', 'rect': [0, -50, 300, 50]},
                 {'layer': 'metal2', 'netName': 'y', 'rect': [200, -50, 600, 50]}]
    data = {"bbox": [0, -50, 600, 50], "terminals": terminals,
            "globalRoutes": [], "globalRouteGrid": []}
    with pytest.raises(AssertionError):
        removeDuplicates(data)


def test_underlapping():
    terminals = [{'layer': 'metal2', 'netName': 'x', 'rect': [0, -50, 300, 50]},
                 {'layer': 'metal2', 'netName': 'x', 'rect': [100, -50, 200, 50]}]
    data = {"bbox": [0, -50, 300, 50], "terminals": terminals,
            "globalRoutes": [], "globalRouteGrid": []}
    newData = removeDuplicates(data)
    assert len(newData['terminals']) == 1
    assert newData['terminals'][0]['rect'] == [0, -50, 300, 50]


def test_disjoint():
    terminals = [{'layer': 'metal2', 'netName': 'x', 'rect': [0, -50, 300, 50]},
                 {'layer': 'metal2', 'netName': 'x', 'rect': [400, -50, 600, 50]}]
    data = {"bbox": [0, -50, 600, 50], "terminals": terminals,
            "globalRoutes": [], "globalRouteGrid": []}
    newData = removeDuplicates(data)
    assert len(newData['terminals']) == 2
    assert newData['terminals'][0]['rect'] == [0, -50, 300, 50]
    assert newData['terminals'][1]['rect'] == [400, -50, 600, 50]
