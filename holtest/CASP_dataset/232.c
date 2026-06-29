/* This file is part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2007-2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0
*/

/*@
    requires x > -2147483648;
    assigns \nothing;
    ensures \result >= 0;
    behavior positive:
      assumes x >= 0;
      ensures \result == x;
    behavior negative:
      assumes x < 0;
      ensures x != -2147483648 ==> \result == -x;
    complete behaviors positive, negative;
    disjoint behaviors positive, negative;
*/
int abs(int x) {
    if (x < 0) {
        return -x;
    }
    return x;
}