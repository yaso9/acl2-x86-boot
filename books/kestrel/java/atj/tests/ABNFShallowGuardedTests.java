/*
 * Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

// This file is handwritten (not generated)
// for the reason given at the end  of the file abnf.lisp.
// However, it is structured similarly to the test code generated by ATJ.

import edu.kestrel.acl2.aij.*;

public class ABNFShallowGuardedTests {

    // Obtain an ACL2 list of natural numbers from the specified file.
    private static Acl2Value getInputFromFile(String filename)
        throws java.io.FileNotFoundException, java.io.IOException {
        java.io.FileInputStream file = new java.io.FileInputStream(filename);
        java.util.List<Integer> bytes = new java.util.ArrayList<>();
        int byt = file.read();
        while (byt != -1) { // EOF
            bytes.add(byt);
            byt = file.read();
        }
        file.close();
        java.util.Collections.reverse(bytes);
        Acl2Value list = Acl2Symbol.NIL;
        for (Integer nat : bytes)
            list = Acl2ConsPair.make(Acl2Integer.make(nat), list);
        return list;
    }

    private static boolean failures = false;

    private static void test_Parse(String testName, Acl2Value input, int n, int m)
        throws Acl2UndefinedPackageException,
               java.io.FileNotFoundException, java.io.IOException {
        System.out.print("Testing '" + testName + "'...");
        boolean pass = true;
        long[] times = n != 0 ? new long[n] : null;
        long minTime = 0;
        long maxTime = 0;
        long sumTime = 0;
        int i = 0;
        do {
            Acl2Value resultJava = null;
            long startTime = System.currentTimeMillis();
            for (int j = 0; j < m; ++j) {
                resultJava = ABNFShallowGuarded.ABNF.parse_grammar(input);
            }
            long endTime = System.currentTimeMillis();
            // we just check that the result is not nil:
            pass = pass && !Acl2Symbol.NIL.equals(resultJava);
            if (n != 0) {
                long time = endTime - startTime;
                times[i] = time;
                sumTime = sumTime + time;
                if (i == 0 || time < minTime) {
                    minTime = time;
                }
                if (time > maxTime) {
                    maxTime = time;
                }
            }
            ++i;
        } while (i < n);
        if (pass) {
            System.out.println(" PASS");
        } else {
            System.out.println(" FAIL");
            failures = true;
        }
        if (n != 0) {
            System.out.println("  Times:");
            for (i = 0; i < n; ++i) {
                System.out.format("    %.3f%n", times[i] / 1000.0);
            }
            System.out.format("  Minimum: %.3f%n", minTime / 1000.0);
            System.out.format("  Average: %.3f%n", sumTime / 1000.0 / n);
            System.out.format("  Maximum: %.3f%n", maxTime / 1000.0);
            System.out.println();
        }
    }

    private static void test_ParseABNFCore(int n, int m)
        throws Acl2UndefinedPackageException,
               java.io.FileNotFoundException, java.io.IOException {
        String testName = "ParseABNFCore";
        Acl2Value input = getInputFromFile("../../../abnf/core-rules.txt");
        test_Parse(testName, input, n, m);
    }

    private static void test_ParseABNFSyntax(int n, int m)
        throws Acl2UndefinedPackageException,
               java.io.FileNotFoundException, java.io.IOException {
        String testName = "ParseABNFSyntax";
        Acl2Value input =
            getInputFromFile("../../../abnf/concrete-syntax-rules.txt");
        test_Parse(testName, input, n, m);
    }

    private static void test_ParseJSON(int n, int m)
        throws Acl2UndefinedPackageException,
               java.io.FileNotFoundException, java.io.IOException {
        String testName = "ParseJSON";
        Acl2Value input = getInputFromFile("../../../abnf/json-grammar.txt");
        test_Parse(testName, input, n, m);
    }

    private static void test_ParseURI(int n, int m)
        throws Acl2UndefinedPackageException,
               java.io.FileNotFoundException, java.io.IOException {
        String testName = "ParseURI";
        Acl2Value input = getInputFromFile("../../../abnf/uri-grammar.txt");
        test_Parse(testName, input, n, m);
    }

    private static void test_ParseHTTP(int n, int m)
        throws Acl2UndefinedPackageException,
               java.io.FileNotFoundException, java.io.IOException {
        String testName = "ParseHTTP";
        Acl2Value input = getInputFromFile("../../../abnf/http-grammar.txt");
        test_Parse(testName, input, n, m);
    }

    private static void test_ParseIMF(int n, int m)
        throws Acl2UndefinedPackageException,
               java.io.FileNotFoundException, java.io.IOException {
        String testName = "ParseIMF";
        Acl2Value input = getInputFromFile("../../../abnf/imf-grammar.txt");
        test_Parse(testName, input, n, m);
    }

    private static void test_ParseSMTP(int n, int m)
        throws Acl2UndefinedPackageException,
               java.io.FileNotFoundException, java.io.IOException {
        String testName = "ParseSMTP";
        Acl2Value input = getInputFromFile("../../../abnf/smtp-grammar.txt");
        test_Parse(testName, input, n, m);
    }

    private static void test_ParseIMAP(int n, int m)
        throws Acl2UndefinedPackageException,
               java.io.FileNotFoundException, java.io.IOException {
        String testName = "ParseIMAP";
        Acl2Value input = getInputFromFile("../../../abnf/imap-grammar.txt");
        test_Parse(testName, input, n, m);
    }

    private static void test_ParseJavaLexical(int n, int m)
        throws Acl2UndefinedPackageException,
               java.io.FileNotFoundException, java.io.IOException {
        String testName = "ParseJavaLexical";
        Acl2Value input =
            getInputFromFile("../../../java/language/lexical-grammar.txt");
        test_Parse(testName, input, n, m);
    }

    private static void test_ParseJavaSyntactic(int n, int m)
        throws Acl2UndefinedPackageException,
               java.io.FileNotFoundException, java.io.IOException {
        String testName = "ParseJavaSyntactic";
        Acl2Value input =
            getInputFromFile("../../../java/language/syntactic-grammar.txt");
        test_Parse(testName, input, n, m);
    }

    private static void test_ParseYul(int n, int m)
        throws Acl2UndefinedPackageException,
               java.io.FileNotFoundException, java.io.IOException {
        String testName = "ParseYul";
        Acl2Value input =
            getInputFromFile("../../../yul/language/abnf-grammar-new.txt");
        test_Parse(testName, input, n, m);
    }

    public static void main(String[] args)
        throws Acl2UndefinedPackageException,
               java.io.FileNotFoundException, java.io.IOException {
        int n = 0;
        if (args.length >= 1) {
            n = Integer.parseInt(args[0]);
        }
        int m = 1;
        if (args.length >= 2) {
            m = Integer.parseInt(args[1]);
        }
        if (args.length >= 3) {
            throw new IllegalArgumentException
                ("There must be 0 or 1 or 2 arguments.");
        }
        ABNFShallowGuarded.initialize();
        test_ParseABNFCore(n, m);
        test_ParseABNFSyntax(n, m);
        test_ParseJSON(n, m);
        test_ParseURI(n, m);
        test_ParseHTTP(n, m);
        test_ParseIMF(n, m);
        test_ParseSMTP(n, m);
        test_ParseIMAP(n, m);
        test_ParseJavaLexical(n, m);
        test_ParseJavaSyntactic(n, m);
        test_ParseYul(n, m);
        if (failures) {
            System.out.println("Some tests failed.");
            System.exit(1);
        } else {
            System.out.println("All tests passed.");
            System.exit(0);
        }
    }
}
