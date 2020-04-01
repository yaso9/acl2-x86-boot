/*
 * Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

package edu.kestrel.acl2.aij;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class Acl2CharacterTest {

    @Test
    void makeWrong() {
        assertThrows(IllegalArgumentException.class,
                () -> Acl2Character.make('\u0100'));
        assertThrows(IllegalArgumentException.class,
                () -> Acl2Character.make('\ua802'));
        assertThrows(IllegalArgumentException.class,
                () -> Acl2Character.make('\uffff'));
    }

    @Test
    void makeRight() {
        assertDoesNotThrow(() -> Acl2Character.make('\0'));
        assertDoesNotThrow(() -> Acl2Character.make('A'));
        assertDoesNotThrow(() -> Acl2Character.make('x'));
        assertDoesNotThrow(() -> Acl2Character.make('5'));
        assertDoesNotThrow(() -> Acl2Character.make('?'));
        assertDoesNotThrow(() -> Acl2Character.make(' '));
        assertDoesNotThrow(() -> Acl2Character.make('*'));
        assertDoesNotThrow(() -> Acl2Character.make('\n'));
        assertDoesNotThrow(() -> Acl2Character.make('\200'));
        assertDoesNotThrow(() -> Acl2Character.make('\300'));
        assertDoesNotThrow(() -> Acl2Character.make('\u00ff'));
    }

    @Test
    void getJavaCharFromConstant() {
        assertEquals(Acl2Character.CODE_0.getJavaChar(), '\0');
    }

    @Test
    void getJavaCharFromMake() {
        assertEquals(Acl2Character.make('a').getJavaChar(), 'a');
        assertEquals(Acl2Character.make('\7').getJavaChar(), '\7');
        assertEquals(Acl2Character.make('|').getJavaChar(), '|');
        assertEquals(Acl2Character.make('\u00f0').getJavaChar(), '\u00f0');
    }

    @Test
    void toStringFromConstant() {
        assertEquals(Acl2Character.CODE_0.toString(), "#\\00");
    }

    @Test
    void toStringFromMakeNormal() {
        assertEquals(Acl2Character.make('c').toString(), "#\\c");
        assertEquals(Acl2Character.make('F').toString(), "#\\F");
        assertEquals(Acl2Character.make('*').toString(), "#\\*");
        assertEquals(Acl2Character.make('%').toString(), "#\\%");
    }

    @Test
    void toStringFromMakeSpecial() {
        assertEquals(Acl2Character.make(' ').toString(), "#\\Space");
        assertEquals(Acl2Character.make('\t').toString(), "#\\Tab");
        assertEquals(Acl2Character.make('\n').toString(), "#\\Newline");
        assertEquals(Acl2Character.make('\f').toString(), "#\\Page");
        assertEquals(Acl2Character.make('\r').toString(), "#\\Return");
        assertEquals(Acl2Character.make('\177').toString(), "#\\Rubout");
    }

    @Test
    void toStringFromMakeHex() {
        assertEquals(Acl2Character.make('\u0000').toString(), "#\\00");
        assertEquals(Acl2Character.make('\u00ff').toString(), "#\\ff");
        assertEquals(Acl2Character.make('\u00b2').toString(), "#\\b2");
        assertEquals(Acl2Character.make('\u0014').toString(), "#\\14");
    }

}
