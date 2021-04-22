# Debugging C++ code called from Python

This command will build the ALIGN environment with debug symbols:
```bash
pip install -e .[test] --no-build-isolation --verbose
```
## Command-line `gdb`

You can now debug the C++ code using command-line `gdb`. Let's do this for the `cascode_current_mirror_ota` example, which is a small design with an intermediate level of hierarchy.

To do this, create a `work` directory, and a subdirectory under that:
```bash
cd $ALIGN_HOME
mkdir -p work/cascode_current_mirror_ota
cd work/cascode_current_mirror_ota
```
Then to run command-line `gdb` on the python executable:
```bash
gdb python
```
You can set breakpoints if you like, for example:
```bash
b Router::RouteWork
```
Not to start,
```bash
run $VENV/bin/schematic2layout.py $ALIGN_HOME/examples/cascode_current_mirror_ota -c
```
where `$VENV` is the path to your virtual environment.

## Debugging using the Visual Studio Code IDE

You can also do similar debugging using vscode.
For this, set up the same sub-directory:
```bash
cd $ALIGN_HOME
mkdir -p work/cascode_current_mirror_ota
cd work/cascode_current_mirror_ota
```

Then add two .json files to setup a debug configuration.
```bash
mkdir .vscode
cat > .vscode/launch.json << EOF
{
    "configurations": [
        {
            "name": "(gdb) Launch",
            "type": "cppdbg",
            "request": "launch",
            "program": "${workspaceFolder}/../../align-venv/bin/python",
            "args": [
                "${workspaceFolder}/../../align-venv/bin/schematic2layout.py",
                "${workspaceFolder}/../../examples/cascode_current_mirror_ota",
                "-c",
                "-n",
                "2"
            ],
            "stopAtEntry": false,
            "cwd": "${workspaceFolder}",
            "environment": [],
            "externalConsole": false,
            "MIMode": "gdb",
            "setupCommands": [
                {
                    "description": "Enable pretty-printing for gdb",
                    "text": "-enable-pretty-printing",
                    "ignoreFailures": true
                }
            ]
        }
    ]
}
EOF

cat > .vscode/c_cpp_properties.json << EOF
{
    "configurations": [
        {
            "name": "Linux",
            "includePath": [
                "${workspaceFolder}/**",
                "${workspaceFolder}/../../_skbuild/linux-x86_64-3.8/cmake-build/_deps/json-src/include",
                "${workspaceFolder}/../../_skbuild/linux-x86_64-3.8/cmake-build/_deps/spdlog-src/include",
                "/usr/include/python3.8"
            ],
            "defines": [],
            "compilerPath": "/usr/bin/clang",
            "cStandard": "c11",
            "cppStandard": "c++14",
            "intelliSenseMode": "linux-clang-x64"
        }
    ],
    "version": 4
}
EOF
