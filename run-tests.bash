#!/bin/bash

set -x

if ! grep '^status = true$' <(./glasgow_subgraph_solver --format lad test-instances/small test-instances/large ) ; then
    echo "non-induced test failed" 1>&1
    exit 1
fi

if ! grep '^status = false$' <(./glasgow_subgraph_solver --induced --format lad test-instances/small test-instances/large ) ; then
    echo "induced test failed" 1>&1
    exit 1
fi

if ! grep '^solution_count = 6$' <(./glasgow_subgraph_solver --count-solutions --format lad test-instances/small test-instances/large ) ; then
    echo "non-induced enumerate test failed" 1>&1
    exit 1
fi

if ! grep '^solution_count = 12$' <(./glasgow_subgraph_solver --count-solutions test-instances/trident.csv test-instances/longtrident.csv ) ; then
    echo "trident enumerate test failed" 1>&1
    exit 1
fi

if ! grep '^solution_count = 6$' <(./glasgow_subgraph_solver --count-solutions --induced test-instances/c3.csv test-instances/c3c2.csv ) ; then
    echo "induced cyclic enumerate test failed" 1>&1
    exit 1
fi

if ! grep '^solution_count = 474$' <(./glasgow_subgraph_solver --count-solutions --format csv test-instances/c3.csv test-instances/c3c2.csv ) ; then
    echo "cyclic enumerate test failed" 1>&1
    exit 1
fi

if ! grep '^solution_count = 6$' <(./glasgow_subgraph_solver --count-solutions --induced --format csv test-instances/c3_with_labels.csv test-instances/c3c2_with_labels.csv ) ; then
    echo "induced cyclic enumerate with channels test failed" 1>&1
    exit 1
fi

if ! grep '^solution_count = 123$' <(./glasgow_subgraph_solver --count-solutions --format csv test-instances/c3_with_labels.csv test-instances/c3c2_with_labels.csv ) ; then
    echo "cyclic enumerate test with labels failed" 1>&1
    exit 1
fi

if ! grep '^solution_count = 1$' <(./glasgow_subgraph_solver --count-solutions --format csv test-instances/small_multigraph_pattern.csv test-instances/small_multigraph_world.csv ) ; then
    echo "simple multigraph test failed" 1>&1
    exit 1
fi

if ! grep '^solution_count = 1$' <(./glasgow_subgraph_solver --count-solutions --format csv test-instances/multigraph_single_edge_pattern.csv test-instances/multigraph_single_edge_target.csv ) ; then
    echo "single edge directed multigraph test failed" 1>&1
    exit 1
fi

if ! grep '^solution_count = 0$' <(./glasgow_subgraph_solver --count-solutions --format csv test-instances/multigraph_single_edge_pattern_fails.csv test-instances/multigraph_single_edge_target.csv ) ; then
    echo "single edge directed multigraph test should have failed, but did not" 1>&1
    exit 1
fi

true

