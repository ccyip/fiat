The Verified Protocol Buffer Compiler
=====================================

## Dependencies

Our specification and implementation are test in Coq 8.8.1 (compiled with OCaml
4.06.0).

In order to run the official example implementation and conformance test, we
need to build the offical Protocol Buffer first. The version used in our
experiment is 3.6.1.

The detailed instructions can be found on its website. But we also list the
steps here for reference.

### To build the library

```
$ git clone https://github.com/protocolbuffers/protobuf.git
$ cd protobuf
$ git checkout v3.6.1
$ ./configure
$ make
```

### To build the example

```
$ cd examples && make cpp
```

The executable programs `add_person_cpp` and `list_people_cpp` will be generated
in the examples directory.

### To build the conformance test runner

```
$ cd conformance && make conformance-test-runner
```

The executable program `conformance-test-runner` will be generated in the conformance directory.

We use a Python test client as a proxy for conformance test since we do not
support oneof type which is used in the test request and response messages. In
order to run the Python client, we have to install protobuf for Python. This
package should be available in most package managers, e.g. pip:

```
$ pip install protobuf
```

## Compiling the code

Run `make` command in the root directory of this archive, or in the Protobuf
subdirectory (`src/Protobuf`).
  * To build the core library: `make protobuf`
  * To build the example: `make protobuf-example`
  * To build the conformance test client: `make protobuf-conformance`
  * To build all of above: `make protobuf-all`

## Runing the example

After compiling, programs `add_person` and `list_people` are generated in the
directory `src/Protobuf/examples`. We could create, list and add person
information into a database.

```
$ ./add_person test.data
$ ./list_people test.data
```

A sample database file `test.data` is available in the archive. We can run the
official implementation `add_person_cpp` and `list_people_cpp` against the same
database and check they behave the same way as our implementation.

## Running the conformance test

After compiling, program `conformance` is generated in the directory
`src/Protobuf/conformance`. We run the conformance test in this directory.

```
$ /path/to/conformance-test-runner --enforce_recommended --failure_list failure_list.txt ./conformance_client.py
```

One could understand the options by running:
```
$ /path/to/conformance-test-runner -h
```

`failure_list.txt` contains all the test cases that we expect to fail. Comments
in this file explained why we fail.

One could also check what test cases we skipped by looking into
`conformance_client.py`. (The test cases we skipped are JSON and Protocol Buffer
version 2 testing)
