#!/usr/bin/env bash

################################################################################

# Java Library
#
# Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
#
# License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
#
# Author: Alessandro Coglio (coglio@kestrel.edu)

################################################################################

# This file compiles all the Java files generated by ATJ
# and all the handwritten test harness Java files.

# This file assumes that
# a Java 8 (or later) compiler and related tools (e.g. the latest OpenJDK)
# is in the path.

################################################################################

# stop on error:
set -e

# generate class files:
javac -cp ../../aij/java/out/artifacts/AIJ_jar/AIJ.jar \
      *.java \
      packages1/*.java \
      packages2/p/*.java \
      packages3/edu/kestrel/*.java
