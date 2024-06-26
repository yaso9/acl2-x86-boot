# Java Library
#
# Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
#
# License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
#
# Author: Alessandro Coglio (coglio@kestrel.edu)

################################################################################

# This file compiles the Java source files of AIJ without IntelliJ IDEA.
# It generates the class and jar files in the same places as IntelliJ IDEA does.

# This file also generates Javadoc HTML documentation
# for public, package-private, and private classes and members
# (not for protected classes and members
# because AIJ currently does not have any).
# The generated documentation goes into the directories
# javadoc-public, javadoc-package, and javadoc-private,
# from where it can be opened in a browser.

# This file also certifies the ACL2 files in this directory.
# Note that the ACL2 files do not depend on the Java-related files,
# and that the Java-related files do not depend on the ACL2 files.
# This file does not assume cert.pl and clean.pl to be in the path:
# it references them via a relative path from this directory.

# This file assumes that
# a Java 8 (or later) compiler and related tools (e.g. the latest OpenJDK)
# is in the path.
# We compile the file requiring the source to be Java 8,
# and ensuring that the class files are Java 8.

################################################################################

$(info ) # print a blank line

all: aij javadoc-all acl2-files

aij: java/out/artifacts/AIJ_jar/AIJ.jar

java/out/artifacts/AIJ_jar/AIJ.jar: java/src/edu/kestrel/acl2/aij/*.java
	@echo "Generate class files:"
	mkdir -p java/out/production/AIJ
	javac -target 8 -source 8 -d java/out/production/AIJ java/src/edu/kestrel/acl2/aij/*.java
	@echo ""
	@echo "Generate jar file:"
	mkdir -p java/out/artifacts/AIJ_jar
	jar cfm java/out/artifacts/AIJ_jar/AIJ.jar java/META-INF/MANIFEST.MF \
            -C java/out/production/AIJ/ .
	@echo ""

javadoc-all: javadoc-public javadoc-package javadoc-private

javadoc-public: javadoc-public/index.html

javadoc-package: javadoc-package/index.html

javadoc-private: javadoc-private/index.html

javadoc-public/index.html: java/src/edu/kestrel/acl2/aij/*.java
	@echo "Generate public Javadoc documentation:"
	javadoc -d javadoc-public -public java/src/edu/kestrel/acl2/aij/*.java
	@echo ""

javadoc-package/index.html: java/src/edu/kestrel/acl2/aij/*.java
	@echo "Generate package Javadoc documentation:"
	javadoc -d javadoc-package -package java/src/edu/kestrel/acl2/aij/*.java
	@echo ""

javadoc-private/index.html: java/src/edu/kestrel/acl2/aij/*.java
	@echo "Generate private Javadoc documentation:"
	javadoc -d javadoc-private -private java/src/edu/kestrel/acl2/aij/*.java
	@echo ""

acl2-files: top.cert

top.cert: top.lisp
	@echo "Certify ACL2 files:"
	../../../build/cert.pl *.lisp
	@echo ""

clean:
	@echo "Delete class files and jar file:"
	/bin/rm -rf java/out
	@echo ""
	@echo "Delete Javadoc HTML files:"
	/bin/rm -rf javadoc-public
	/bin/rm -rf javadoc-package
	/bin/rm -rf javadoc-private
	@echo ""
	@echo "Delete ACL2 certification files:"
	../../../build/clean.pl
	@echo ""
