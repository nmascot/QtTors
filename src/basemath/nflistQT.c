/* Copyright (C) 2021  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

#include "pari.h"
#include "paripriv.h"

static GEN /* -t */
pol_mx(long v) { return deg1pol_shallow(gen_m1, gen_0, v); }
static GEN QT4(long k, long v)
{ switch(k) {
  case 1: return mkpoln(5, gen_1, pol_x(v), stoi(-6), pol_mx(v), gen_1);
  case 2: return mkpoln(5, gen_1, gen_0, pol_x(v), gen_0, gen_1);
  case 3: return mkpoln(5, gen_1, pol_x(v), gen_0, pol_x(v), gen_1);
  default: return NULL; }}
static GEN QT5(long k, long v)
{ GEN a3, a2, a1, a0;
  switch(k) {
  case 1:
  a3 = mkpoln(4, stoi(-2), stoi(-6), stoi(-10), stoi(-10)); setvarn(a3,v);
  a2 = mkpoln(5, gen_1, stoi(5), stoi(11), stoi(15), stoi(5)); setvarn(a2,v);
  a1 = mkpoln(4, gen_1, stoi(4), stoi(10), stoi(10)); setvarn(a1,v);
  return mkpoln(6, gen_1, pol_xn(2,v), a3, a2, a1, gen_1);
  case 2:
  a3 = deg1pol_shallow(gen_m1, stoi(-50), v);
  a1 = deg1pol_shallow(stoi(5), stoi(625), v);
  a0 = deg1pol_shallow(stoi(-3), gen_0, v);
  return mkpoln(6, gen_1, gen_0, a3, pol_mx(v), a1, a0);
  case 3:
  a2 = deg1pol_shallow(stoi(5), gen_0, v);
  a0 = deg2pol_shallow(gen_1, gen_m1, stoi(16), v);
  return mkpoln(6, gen_1, gen_0, stoi(10), a2, stoi(-15), a0);
  default: return NULL; }}
static GEN QT6(long k, long v)
{ GEN a5, a4, a3, a2, a1, a0;
  switch(k) {
  case 1:
  a5 = deg1pol_shallow(gen_2, gen_0, v);
  a4 = deg1pol_shallow(stoi(-5), stoi(-15), v);
  a2 = deg1pol_shallow(stoi(5), gen_0, v);
  a1 = deg1pol_shallow(gen_m2, stoi(-6), v);
  return mkpoln(7, gen_1, a5, a4, stoi(20), a2, a1, gen_1);
  case 2:
  a0 = deg2pol_shallow(stoi(3), gen_0, stoi(4), v);
  return mkpoln(7, gen_1, gen_0, stoi(6), gen_0, stoi(9), gen_0, a0);
  case 3:
  return mkpoln(7, gen_1, gen_0, stoi(6), gen_0, stoi(9), gen_0, pol_mx(v));
  case 4:
  a2 = deg1pol_shallow(gen_1, stoi(-3), v);
  return mkpoln(7, gen_1, gen_0, pol_x(v), gen_0, a2, gen_0, gen_m1);
  case 5:
  a4 = deg1pol_shallow(gen_1, stoi(-6), v);
  a3 = deg1pol_shallow(gen_2, gen_m2, v);
  a2 = deg1pol_shallow(gen_1, stoi(9), v);
  return mkpoln(7, gen_1, gen_0, a4, a3, a2, stoi(6), gen_1);
  case 6:
  a2 = mkpoln(5,stoi(-12),gen_0,stoi(-36),gen_0,gen_0); setvarn(a2,v);
  a0 = mkpoln(7,stoi(16),gen_0,stoi(48),gen_0,gen_0,gen_0,gen_0); setvarn(a0,v);
  return mkpoln(7, gen_1, gen_0, gen_0, gen_0, a2, gen_0, a0);
  case 7: return mkpoln(7, gen_1,gen_0,gen_0,gen_0,pol_x(v),gen_0,gen_m1);
  case 8:
  a0 = deg2pol_shallow(stoi(3), gen_0, stoi(4), v);
  return mkpoln(7, gen_1,gen_0,stoi(-3),gen_0,gen_0,gen_0,a0);
  case 9:
  a4 = deg2pol_shallow(stoi(3), gen_0, stoi(-6), v);
  a3 = deg2pol_shallow(gen_m2, gen_0, stoi(4), v);
  return mkpoln(7, gen_1,gen_0,a4,a3,stoi(9),stoi(-12),stoi(4));
  case 10:
  a0 = deg2pol_shallow(gen_m1, gen_0, stoi(-1024), v);
  return mkpoln(7, gen_1,stoi(-12),stoi(36),gen_0,gen_0,gen_0,a0);
  case 11:
  a0 = deg1pol_shallow(gen_1, stoi(4), v);
  return mkpoln(7, gen_1,gen_0,stoi(-3),gen_0,gen_0,gen_0,a0);
  case 12:
  a5 = deg2pol_shallow(stoi(10), gen_0, stoi(-50), v);
  a4 = gtopoly(mkvecsmall5(55, 0L,-550L, 0L, 1375L), v);
  a3 = gtopoly(mkvecsmalln(7, 140L, 0L,-2100L, 0L, 10500L, 0L,-17500L), v);
  a2 = gtopoly(mkvecsmalln(9, 175L, 0L,-3500L, 0L, 26250L, 0L,-87500L, 0L, 109375L), v);
  a1 = gtopoly(mkvecsmalln(11, 106L, 0L,-1370L, 0L, 900L, 0L, 59500L, 0L,-308750L, 0L, 468750L), v);
  a0 = gtopoly(mkvecsmalln(13, 25L, 0L,-750L, 0L, 9375L, 0L,-62500L, 0L, 234375L, 0L,-468750L, 0L, 390625L), v);
  return mkpoln(7, gen_1,a5,a4,a3,a2,a1,a0);
  case 13:
  return mkpoln(7, gen_1,gen_m2,gen_1,gen_0,gen_0,gen_0,pol_mx(v));
  case 14:
  return mkpoln(7, gen_1,stoi(4),stoi(20),gen_0,gen_0,pol_mx(v),pol_x(v));
  default: return NULL; }}
static GEN QT7(long k, long v)
{ GEN a6, a5, a4, a3, a2, a1, a0;
  switch(k) {
  case 1:
  a6 = gtopoly(mkvecsmall4(1, 2L,-1L, 13L), v);
  a5 = gtopoly(mkvecsmalln(6, 3L,-3L, 9L, 24L,-21L, 54L), v);
  a4 = gtopoly(mkvecsmalln(8, 3L,-9L, 27L,-22L, 6L, 84L,-121L, 75L), v);
  a3 = gtopoly(mkvecsmalln(10, 1L,-6L, 22L,-57L, 82L,-70L,-87L, 140L,-225L,-2L), v);
  a2 = gtopoly(mkvecsmalln(11, -1L, 5L,-25L, 61L,-126L, 117L,-58L,-155L, 168L,-80L,-44L), v);
  a1 = gtopoly(mkvecsmalln(11, -1L, 8L,-30L, 75L,-102L, 89L, 34L,-56L, 113L, 42L,-17L), v);
  a0 = gtopoly(mkvecsmalln(10, 1L,-7L, 23L,-42L, 28L, 19L,-60L,-2L, 16L,-1L), v);
  return mkpoln(8, gen_1,a6,a5,a4,a3,a2,a1,a0);
  case 2:
  a5 = gtopoly(mkvecsmall4(-147L,-735L,-441L,-21L), v);
  a4 = gtopoly(mkvecsmall5(-686L,-3920L,-4508L,-1568L,-70L), v);
  a3 = gtopoly(mkvecsmalln(7, 7203L, 67914L, 183505L, 107996L, 8085L,-1862L,-105L), v);
  a2 = gtopoly(mkvecsmalln(8, 67228L, 547428L, 1373372L, 1227940L, 416500L, 38220L,-588L,-84L), v);
  a1 = gtopoly(mkvecsmalln(10, -117649L,-1563051L,-6809236L,-10708460L,-4050830L, 788214L, 402780L, 37828L, 343L,-35L), v);
  a0 = gtopoly(mkvecsmalln(11, -1647086L,-16893436L,-56197806L,-69977488L,-44893212L,-13304872L,-624652L, 103152L, 11466L, 196L,-6L), v);
  return mkpoln(8, gen_1,gen_0,a5,a4,a3,a2,a1,a0);
  case 3:
  a5 = gtopoly(readseq((char*)"[-21,0,-1176,147,-20580,3969,-107163]"), v);
  a4 = gtopoly(readseq((char*)"[-21,49,-1715,4214,-51107,129850,-653905,1648458,-3000564,6751269]"), v);
  a3 = gtopoly(readseq((char*)"[91,98,9849,8673,427133,291354,9385460,4618152,108334149,35173278,608864445,114771573,1275989841]"), v);
  a2 = gtopoly(readseq((char*)"[112,-49,14651,-10682,800513,-821730,23571744,-30983190,401636536,-628991685,3929562693,-6832117530,20190045015,-35916751080,40831674912,-68903451414]"), v);
  a1 = gtopoly(readseq((char*)"[-84,-98,-14896,-16709,-1127098,-1228626,-47347279,-51034970,-1201635330,-1316073164,-18735012261,-21705143929,-173551408569,-224605199322,-861876002232,-1329675932088,-1728966234555,-3376269119286,0]"), v);
  a0 = gtopoly(readseq((char*)"[-97,-14,-19803,-903,-1765232,84609,-89982172,11950757,-2882068329,588528171,-59885187418,15296374002,-801314604769,222442927665,-6560078164731,1705024373220,-28577589326937,5543939564730,-38647180304208,4961048501808,74415727527120,25115308040403]"), v);
  return mkpoln(8, gen_1,gen_0,a5,a4,a3,a2,a1,a0);
  case 4:
  a4 = deg2pol_shallow(stoi(-7), gen_0, stoi(98), v);
  a3 = deg1pol_shallow(stoi(28), stoi(441), v);
  a2 = gtopoly(mkvecsmall4(-35L,-112L,-196L, 343L), v);
  a1 = deg2pol_shallow(stoi(7), stoi(196), stoi(1372), v);
  a0 = gtopoly(mkvecsmalln(6, -1L,-30L,-259L,-588L,-1372L, 0L), v);
  return mkpoln(8, gen_1,stoi(7),stoi(42),a4,a3,a2,a1,a0);
  case 5:
  a3 = deg1pol_shallow(stoi(12), stoi(7203), v);
  a2 = deg1pol_shallow(stoi(-30), gen_0, v);
  a1 = deg1pol_shallow(stoi(28), stoi(-117649), v);
  a0 = deg1pol_shallow(stoi(-9), gen_0, v);
  return mkpoln(8, gen_1,gen_0,stoi(-147),pol_mx(v),a3,a2,a1,a0);
  default: return NULL; }}

static GEN QT8(long k, long v)
{ GEN a7, a6, a5, a4, a3, a2, a1, a0, l, l2;
  switch(k) {
  case 1:
  a6 = gtopoly(mkvecsmall5(-1L, 0L,-12L, 0L,-4L), v);
  a4 = gtopoly(mkvecsmalln(7, 3L, 0L, 37L, 0L, 24L, 0L, 4L), v);
  a2 = gtopoly(mkvecsmalln(9, -3L, 0L,-38L, 0L,-36L, 0L,-8L, 0L, 0L), v);
  a0 = gtopoly(mkvecsmalln(11, 1L, 0L, 12L, 0L, 4L, 0L, 0L, 0L, 0L, 0L, 0L), v);
  return mkpoln(9, gen_1,gen_0,a6,gen_0,a4,gen_0,a2,gen_0,a0);
  case 2:
  a7 = deg2pol_shallow(gen_m1, gen_0, gen_0, v);
  a6 = deg2pol_shallow(stoi(-7), gen_0, stoi(-12), v);
  a5 = gtopoly(mkvecsmall5(1L, 0L,-3L, 0L, 0L), v);
  a4 = gtopoly(mkvecsmall5(2, 0L, 6L, 0L, 38L), v);
  return mkpoln(9, gen_1,a7,a6,a5,a4,a5,a6,a7,gen_1);
  case 3:
  a6 = deg1pol_shallow(stoi(-12), gen_0, v);
  a4 = deg2pol_shallow(stoi(30), gen_0, stoi(8), v);
  a2 = gtopoly(mkvecsmall4(-28L, 0L, 16L, 0L), v);
  a0 = gtopoly(mkvecsmall5(9, 0L,-24L, 0L, 16L), v);
  return mkpoln(9, gen_1,gen_0,a6,gen_0,a4,gen_0,a2,gen_0,a0);
  case 4:
  a6 = deg2pol_shallow(stoi(-10), gen_0, stoi(40), v);
  a4 = gtopoly(mkvecsmall5(33, 0L,-208L, 0L, 472L), v);
  a2 = gtopoly(mkvecsmalln(7, -40L, 0L, 200L, 0L,-520L, 0L, 1440L), v);
  a0 = gtopoly(mkvecsmalln(9, 16L, 0L, 544L, 0L, 4336L, 0L,-4896L, 0L, 1296L), v);
  return mkpoln(9, gen_1,gen_0,a6,gen_0,a4,gen_0,a2,gen_0,a0);
  case 5:
  a6 = gtopoly(mkvecsmall5(-4L, 0L,-12L, 0L,-8L), v);
  a4 = gtopoly(mkvecsmalln(9, 6L, 0L, 32L, 0L, 58L, 0L, 40L, 0L, 8L), v);
  a2 = gtopoly(mkvecsmalln(13, -4L, 0L,-28L, 0L,-76L, 0L,-100L, 0L,-64L, 0L,-16L, 0L, 0L), v);
  a0 = gtopoly(mkvecsmalln(17, 1L, 0L, 8L, 0L, 26L, 0L, 44L, 0L, 41L, 0L, 20L, 0L, 4L, 0L, 0L, 0L, 0L), v);
  return mkpoln(9, gen_1,gen_0,a6,gen_0,a4,gen_0,a2,gen_0,a0);
  case 6:
  a6 = deg2pol_shallow(gen_m1,stoi(-12),stoi(-4), v);
  a4 = gtopoly(mkvecsmall4(3, 37L, 24L, 4L), v);
  a2 = gtopoly(mkvecsmall5(-3L,-38L,-36L,-8L, 0L), v);
  a0 = gtopoly(mkvecsmalln(6, 1L, 12L, 4L, 0L, 0L, 0L), v);
  return mkpoln(9, gen_1,gen_0,a6,gen_0,a4,gen_0,a2,gen_0,a0);
  case 7:
  a6 = gtopoly(mkvecsmall5(-60L, 432L, -1056L, 864L, -240L), v);
  a4 = gtopoly(mkvecsmalln(9, 690L, -9168L, 51384L, -155376L, 271944L, -278496L, 166560L, -54528L, 7680L), v);
  a2 = gtopoly(mkvecsmalln(13, -1620L, 28944L, -232848L, 1114560L, -3542400L, 7900416L, -12707712L, 14853888L, -12502080L, 7361280L, -2868480L, 663552L, -69120L), v);
  a0 = gtopoly(mkvecsmalln(17, 45L, -1584L, 24984L, -234288L, 1463256L, -6468768L, 21014784L, -51401664L, 96087888L, -138220416L, 152857728L, -128756736L, 81006336L, -36790272L, 11372544L, -2138112L, 184320L), v);
  return mkpoln(9, gen_1,gen_0,a6,gen_0,a4,gen_0,a2,gen_0,a0);
  case 8:
  a6 = gtopoly(mkvecsmalln(9, -16L, 0L, -64L, 0L, -96L, 0L, -80L, 0L, -36L), v);
  a4 = gtopoly(mkvecsmalln(17, 64L, 0L, 576L, 0L, 2304L, 0L, 5296L, 0L, 7568L, 0L, 6896L, 0L, 3920L, 0L, 1116L, 0L, 0L), v);
  a2 = gtopoly(mkvecsmalln(23, -512L, 0L, -5888L, 0L, -29696L, 0L, -86912L, 0L, -164736L, 0L, -213184L, 0L, -191616L, 0L, -116960L, 0L, -44416L, 0L, -8064L, 0L, 0L, 0L, 0L), v);
  a0 = gtopoly(mkvecsmalln(25, -256L, 0L, -3328L, 0L, -18944L, 0L, -62208L, 0L, -130880L, 0L, -185408L, 0L, -180224L, 0L, -118272L, 0L, -48128L, 0L, -9216L, 0L, 0L, 0L, 0L, 0L, 0L), v);
  return mkpoln(9, gen_1,gen_0,a6,gen_0,a4,gen_0,a2,gen_0,a0);
  case 9:
  a4 = deg1pol_shallow(gen_2, gen_m1, v);
  return mkpoln(9, gen_1,gen_0,pol_x(v),gen_0,a4,gen_0,pol_x(v),gen_0,gen_1);
  case 10:
  a6 = gtopoly(mkvecsmall5(2, 0L, 20L, 0L, 18L), v);
  a4 = gtopoly(mkvecsmalln(9, 2L, 0L, 48L, 0L, 316L, 0L, 432L, 0L, 162L), v);
  a2 = gtopoly(mkvecsmalln(13, 2L, 0L, 52L, 0L, 494L, 0L, 2136L, 0L, 4446L, 0L, 4212L, 0L, 1458L), v);
  a0 = gtopoly(mkvecsmalln(17, 1L, 0L, 32L, 0L, 412L, 0L, 2784L, 0L, 10854L, 0L, 25056L, 0L, 33372L, 0L, 23328L, 0L, 6561L), v);
  return mkpoln(9, gen_1,gen_0,a6,gen_0,a4,gen_0,a2,gen_0,a0);
  case 11:
  a6 = deg2pol_shallow(stoi(-4), stoi(-4), gen_0, v);
  a4 = gtopoly(mkvecsmall5(6, 8L, -2L, -4L, 0L), v);
  a2 = gtopoly(mkvecsmalln(7, -4L, -4L, 4L, 4L, 0L, 0L, 0L), v);
  a0 = gtopoly(mkvecsmalln(9, 1L, 0L, -2L, 0L, 1L, 0L, 0L, 0L, 0L), v);
  return mkpoln(9, gen_1,gen_0,a6,gen_0,a4,gen_0,a2,gen_0,a0);
  case 12:
  a6 = deg1pol_shallow(stoi(-22), gen_0, v);
  a4 = deg2pol_shallow(stoi(135), gen_0, gen_0, v);
  a2 = gtopoly(mkvecsmall4(-150L, 0L, 0L, 0L), v);
  return mkpoln(9, gen_1,gen_0,a6,gen_0,a4,gen_0,a2,gen_0,pol_xn(4, v));
  case 13:
  a6 = deg1pol_shallow(stoi(18), gen_0, v);
  a4 = deg2pol_shallow(stoi(81), gen_0, gen_2, v);
  a2 = gtopoly(mkvecsmall4(108, 0L, 2L, 0L), v);
  return mkpoln(9, gen_1,gen_0,a6,gen_0,a4,gen_0,a2,gen_0,gen_1);
  case 14:
  a2 = deg2pol_shallow(stoi(3), gen_0, stoi(3996), v);
  return mkpoln(9, gen_1,gen_0,stoi(-36),gen_0,stoi(486),gen_0,a2,gen_0,stoi(6561));
  case 15:
  a6 = deg2pol_shallow(stoi(-36), gen_0, stoi(4032), v);
  a4 = gtopoly(mkvecsmall5(-108L, -9504L, -76464L, 1064448L, 9918720L), v);
  a2 = gtopoly(mkvecsmalln(6, -1L, -63L, -884L, 2392L, 111552L, 522368L), v);
  a2 = ZX_mulu(a2, 15552);
  a0 = gtopoly(mkvecsmalln(7, -1L,-62L,-1208L,-4914L, 109241L, 1328096L, 4323088L), v);
  a0 = ZX_mulu(a0, 746496);
  return mkpoln(9, gen_1,gen_0,a6,gen_0,a4,gen_0,a2,gen_0,a0);
  case 16:
  {
    GEN a, b;
    a = gtopoly(mkvecsmall5(125, 220L, 334L, 220L, 125L), v);
    b = gtopoly(mkvecsmall5(25, 220L, 534L, 220L, 25L), v);
    a6 = ZX_sqr(a); a4 = ZX_sqr(a6); a2 = ZX_mul(a4, a6);
    a0 = ZX_mul(a2, ZX_mul(a, b));
    a6 = ZX_shifti(a6, 3); a4 = ZX_mulu(a4, 14); a2 = ZX_neg(ZX_shifti(a2, 3));
    return mkpoln(9, gen_1,gen_0,a6,gen_0,a4,gen_0,a2,gen_0,a0);
  }
  case 17:
  a5 = deg1pol_shallow(stoi(7), gen_0, v);
  a3 = deg1pol_shallow(stoi(-7), gen_0, v);
  return mkpoln(9, gen_1,pol_mx(v),stoi(-11),a5,stoi(36),a3,stoi(-11),pol_x(v),gen_1);
  case 18:
  return mkpoln(9, gen_1,gen_0,pol_x(v),gen_0,gen_0,gen_0,pol_x(v),gen_0,gen_1);
  case 19:
  a6 = gtopoly(mkvecsmall5(-1L, 0L, -2, 0L, -1L), v);
  a4 = gtopoly(mkvecsmalln(7, 2L, 0L, 4L, 0L, 4L, 0L, 2L), v);
  a2 = gtopoly(mkvecsmalln(9, -1L, 0L, -3L, 0L, -3L, 0L, -1L, 0L, 0L), v);
  a0 = gtopoly(mkvecsmalln(9, 1L, 0L, 2L, 0L, 1L, 0L, 0L, 0L, 0L), v);
  return mkpoln(9, gen_1,gen_0,a6,gen_0,a4,gen_0,a2,gen_0,a0);
  case 20:
  a6 = deg2pol_shallow(stoi(-4), gen_0, stoi(-4), v);
  a4 = gtopoly(mkvecsmall5(10, 0L, 18L, 0L, 8L), v);
  a2 = gtopoly(mkvecsmalln(7, -12L, 0L, -40L, 0L, -44L, 0L, -16L), v);
  a0 = gtopoly(mkvecsmalln(9, 9L, 0L, 42L, 0L, 73L, 0L, 56L, 0L, 16L), v);
  return mkpoln(9, gen_1,gen_0,a6,gen_0,a4,gen_0,a2,gen_0,a0);
  case 21:
  a4 = gtopoly(mkvecsmalln(7, -16L, 0L, -64L, 0L, -80L, 0L, -16L), v);
  a2 = gtopoly(mkvecsmalln(7, -64L, 0L, -256L, 0L, -320L, 0L, -128L), v);
  a0 = gtopoly(mkvecsmalln(9, 64L, 0L, 192L, 0L, 192L, 0L, 64L, 0L, 0L), v);
  return mkpoln(9, gen_1,gen_0,stoi(8),gen_0,a4,gen_0,a2,gen_0,a0);
  case 22:
  a6 = deg2pol_shallow(stoi(-4), gen_0, stoi(4), v);
  a4 = gtopoly(mkvecsmall5(6, -4L, -14L, 4L, 8L), v);
  a2 = gtopoly(mkvecsmalln(7, -4L, 8L, 8L, -16L, -4L, 8L, 0L), v);
  a0 = gtopoly(mkvecsmalln(9, 1L, -4L, 2L, 8L, -7L, -4L, 4L, 0L, 0L), v);
  return mkpoln(9, gen_1,gen_0,a6,gen_0,a4,gen_0,a2,gen_0,a0);
  case 23:
  a4 = gtopoly(mkvecsmall5(-2L, -8L, 0L, 0L, -54L), v);
  a2 = gtopoly(mkvecsmall5(8, 32L, 0L, 0L, 216L), v);
  a0 = gtopoly(mkvecsmall5(-9L, -36L, 0L, 0L, -243L), v);
  return mkpoln(9, gen_1,gen_0,gen_0,gen_0,a4,gen_0,a2,gen_0,a0);
  case 24:
  a2 = deg1pol_shallow(gen_1, stoi(-4), v);
  return mkpoln(9, gen_1,gen_0,stoi(-4),gen_0,stoi(6),gen_0,a2,gen_0,gen_1);

  case 25:
  l = polcyclo(7,v); l2 = ZX_sqr(l);
  a6 = gtopoly(mkvecsmalln(7, 84L, 84L, -112L, -308L, -700L, -504L, 84L), v);
  a5 = gtopoly(mkvecsmalln(13, 560L, 1120L, -2240L, -6384L, -3472L, 224L, -3920L, -4480L, 5936L, 9296L, 2464L, -448L, 1344L), v);
  a4 = gtopoly(mkvecsmalln(13, 1470L, 2940L, 294L, -11956L, -48216L, -26852L, 120050L, 205016L, 213150L, 196588L, 88788L, 9800L, 12446L), v);
  a3 = gtopoly(mkvecsmalln(19, 2016L, 6048L, 30912L, 32704L, -261408L, -346528L, 1578976L, 4246816L, 2860480L, -268800L, 917728L, 2114336L, -2704800L, -6320608L, -2920736L, 536032L, -47488L, -544320L, 12992L), v);
  a2 = gtopoly(mkvecsmalln(25, 1540L, 6160L, 60284L, 131348L, -151704L, 650524L, 6396656L, 13314560L, 8040452L, -16810472L, -55560596L, -94626644L, -130492684L, -163684500L, -171862684L, -161899080L, -157896284L, -135663472L, -86189824L, -59731196L, -58101064L, -45010196L, -17434872L, 132188L, 2595012L), v);
  a1 = gtopoly(readseq((char*)"[624,3120,44640,136304,271040,3613680,17666880,35886224,22396928,-96335376,-408141440,-784315280,-937605872,-1107758176,-1636450656,-1794879728,-1127976368,-627870656,-562508912,35061152,922496624,1192002304,1164878464,1272919840,1128535184,768008192,548423456,344154608,86020768,-22574848,-9775744]"), v);
  a0 = gtopoly(readseq((char*)"[105,525,11179,33859,167188,2434124,14781438,40653949,-6098631,-352257353,-781450775,-198418052,1352424059,2427447113,4592702177,9723400225,14019045082,15381906736,17922131514,20555126571,18709345473,14941739365,12849159169,10098473476,6233988397,3660253695,2470904919,1309283969,581724381,368757473,193963273]"),v);
  a6 = ZX_mul(a6, l); a5 = ZX_mul(a5, l);
  a4 = ZX_mul(a4, l2); a3 = ZX_mul(a3, l2);
  a2 = ZX_mul(a2, l2); a1 = ZX_mul(a1, l2); a0 = ZX_mul(a0, ZX_mul(l2, l));
  return mkpoln(9, gen_1,gen_0,a6,a5,a4,a3,a2,a1,a0);
  case 26:
  a6 = gtopoly(mkvecsmall5(8, 0L, -16L, 0L, 8L), v);
  a4 = gtopoly(mkvecsmalln(9, 14L, 0L, -56L, 0L, 84L, 0L, -56L, 0L, 14L), v);
  a2 = gtopoly(mkvecsmalln(13, -8L, 0L, 48L, 0L, -120L, 0L, 160L, 0L, -120L, 0L, 48L, 0L, -8L), v);
  a0 = gtopoly(mkvecsmalln(17, 3L, 18L, 6L, -126L, -126L, 378L, 462L, -630L, -840L, 630L, 882L, -378L, -546L, 126L, 186L, -18L, -27L), v);
  return mkpoln(9, gen_1,gen_0,a6,gen_0,a4,gen_0,a2,gen_0,a0);
  case 27:
  a1 = pol_x(v); a3 = deg1pol_shallow(gen_2, gen_0, v);
  return mkpoln(9, gen_1,a1,gen_m2,a3,stoi(-5),a3,gen_m2,a1,gen_1);
  case 28:
  a6 = deg2pol_shallow(gen_2,gen_0,gen_2, v);
  a4 = gtopoly(mkvecsmall5(1, 0L, 4L, 0L, 3L), v);
  a2 = gtopoly(mkvecsmall5(2, 0L, 4L, 0L, 2L), v);
  a0 = gtopoly(mkvecsmall5(1, 0L, 1L, 0L, 0L), v);
  return mkpoln(9, gen_1,gen_0,a6,gen_0,a4,gen_0,a2,gen_0,a0);
  case 29:
  a6 = deg1pol_shallow(stoi(-4), gen_0, v);
  a4 = deg2pol_shallow(stoi(6), gen_m1, gen_m2, v);
  a2 = gtopoly(mkvecsmall4(-4L, 0L, 4L, 0L), v);
  a0 = gtopoly(mkvecsmall5(1, 0L, -2L, 0L, 1L), v);
  return mkpoln(9, gen_1,gen_0,a6,gen_0,a4,gen_0,a2,gen_0,a0);
  case 30:
  a4 = deg2pol_shallow(stoi(-4),gen_0,stoi(8), v);
  a2 = deg2pol_shallow(stoi(16),gen_0,stoi(32), v);
  a0 = gtopoly(mkvecsmall5(4, 0L, 12L, 0L, 0L), v);
  return mkpoln(9, gen_1,gen_0,stoi(-8),gen_0,a4,gen_0,a2,gen_0,a0);
  case 31:
  a4 = gtopoly(mkvecsmall4(-16L, -64L, -80L, -16L), v);
  a2 = gtopoly(mkvecsmall4(-64L, -256L, -320L, -128L), v);
  a0 = gtopoly(mkvecsmall5(64, 192L, 192L, 64L, 0L), v);
  return mkpoln(9, gen_1,gen_0,stoi(8),gen_0,a4,gen_0,a2,gen_0,a0);
  case 32:
  return mkpoln(9, gen_1,gen_0,stoi(-8),gen_0,stoi(18),gen_0,gen_0,gen_0,pol_xn(2,v));
  case 33:
  a6 = deg2pol_shallow(stoi(-4), gen_0, stoi(-108), v);
  a5 = deg2pol_shallow(stoi(-48), gen_0, stoi(-1296), v);
  a4 = gtopoly(mkvecsmall5(6, 0L, -4L, 0L, -4482L), v);
  a3 = gtopoly(mkvecsmall5(96, 0L, 4416L, 0L, 49248L), v);
  a2 = gtopoly(mkvecsmalln(7, -4L, 0L, 140L, 0L, 15284L, 0L, 231876L), v);
  a1 = gtopoly(mkvecsmalln(7, -48L, 0L, -2928L, 0L, -53136L, 0L, -244944L), v);
  a0 = gtopoly(mkvecsmalln(9, 1L, 0L, 36L, 0L, -162L, 0L, -8748L, 0L, 59049L), v);
  return mkpoln(9, gen_1,gen_0,a6,a5,a4,a3,a2,a1,a0);
  case 34:
  a2 = deg2pol_shallow(stoi(12), gen_0, stoi(-30240), v);
  a1 = deg2pol_shallow(stoi(-108), gen_0, stoi(62208), v);
  a0 = deg2pol_shallow(stoi(243), gen_0, stoi(-34992), v);
  return mkpoln(9, gen_1,gen_0,stoi(-72),gen_0,stoi(1944),gen_0,a2,a1,a0);
  case 35:
  a6 = deg1pol_shallow(gen_2,gen_0, v);
  a4 = deg2pol_shallow(gen_1,gen_2,gen_0, v);
  a2 = deg2pol_shallow(gen_2,gen_0,gen_0, v);
  a0 = deg2pol_shallow(gen_2,gen_m1,gen_0, v);
  return mkpoln(9, gen_1,gen_0,a6,gen_0,a4,gen_0,a2,gen_0,a0);
  case 36:
  a6 = deg2pol_shallow(gen_1,gen_0,stoi(108), v);
  a5 = gtopoly(mkvecsmall4(1, 0L, 108L, 216L), v);
  a4 = gtopoly(mkvecsmall5(1, 0L, 108L, 216L, 4374L), v);
  a3 = gtopoly(mkvecsmalln(6, 1L, 0L, 108L, 216L, 4374L, 13608L), v);
  a2 = gtopoly(mkvecsmalln(7, 1L, 0L, 108L, 216L, 4374L, 13608L, 99468L), v);
  a1 = gtopoly(mkvecsmalln(8, 1L, 0L, 108L, 216L, 4374L, 13608L, 99468L, 215784L), v);
  a0 = gtopoly(mkvecsmalln(9, 1L, 0L, 108L, 216L, 4374L, 13608L, 99468L, 215784L, 998001L), v);
  return mkpoln(9, gen_1,pol_x(v),a6,a5,a4,a3,a2,a1,a0);
  case 37:
  a7 = deg2pol_shallow(gen_m1,gen_0,stoi(-7), v);
  a6 = gtopoly(mkvecsmall5(7, 0L, 98L, 0L, 343L), v);
  a1 = gtopoly(mkvecsmalln(13, -756L, 0L, -31752L, 0L, -555660L, 0L, -5186160L, 0L, -27227340L, 0L, -76236552L, 0L, -88942644L), v);
  a0 = gtopoly(mkvecsmalln(15, 756L, 0L, 37044L, 0L, 777924L, 0L, 9075780L, 0L, 63530460L, 0L, 266827932L, 0L, 622598508L, 0L, 622598508L), v);
  return mkpoln(9, gen_1,a7,a6,gen_0,gen_0,gen_0,gen_0,a1,a0);
  case 38:
  a0 = deg2pol_shallow(gen_1, gen_0, stoi(27), v);
  return mkpoln(9, gen_1,gen_0,stoi(-4),gen_0,gen_0,gen_0,gen_0,gen_0,a0);
  case 39:
  return mkpoln(9, gen_1,gen_0,gen_0,gen_0,gen_0,gen_0,pol_x(v),gen_0,gen_1);
  case 40:
  a0 = deg1pol_shallow(gen_1, stoi(-27), v);
  return mkpoln(9, gen_1,gen_0,stoi(-8),gen_0,stoi(18),gen_0,gen_0,gen_0,a0);
  case 41:
  a2 = deg1pol_shallow(stoi(4), stoi(-32), v);
  a1 = deg1pol_shallow(stoi(-12), gen_0, v);
  a0 = deg1pol_shallow(stoi(9), stoi(16), v);
  return mkpoln(9, gen_1,gen_0,stoi(-8),gen_0,stoi(24),gen_0,a2,a1,a0);
  case 42:
  a2 = deg2pol_shallow(stoi(12), gen_0, stoi(-108), v);
  a1 = deg2pol_shallow(stoi(-36), gen_0, gen_0, v);
  a0 = deg2pol_shallow(stoi(27), gen_0, stoi(81), v);
  return mkpoln(9, gen_1,gen_0,stoi(-12),gen_0,stoi(54),gen_0,a2,a1,a0);
  case 43:
  return mkpoln(9, gen_1,gen_m1,stoi(7),gen_0,gen_0,gen_0,gen_0,pol_mx(v),pol_x(v));
  case 44:
  return mkpoln(9, gen_1,pol_x(v),gen_0,gen_0,gen_0,gen_0,gen_0,pol_x(v),gen_1);
  case 45:
  a2 = deg1pol_shallow(stoi(4),stoi(-108),v);
  a1 = deg1pol_shallow(stoi(-12),gen_0,v);
  a0 = deg1pol_shallow(stoi(9),stoi(81),v);
  return mkpoln(9, gen_1,gen_0,stoi(-12),gen_0,stoi(54),gen_0,a2,a1,a0);
  case 46:
  a5 = deg2pol_shallow(stoi(4), gen_0, stoi(8), v);
  a4 = deg2pol_shallow(stoi(-3), gen_0, stoi(-6), v);
  return mkpoln(9, gen_1,gen_0,gen_0,a5,a4,gen_0,stoi(16),stoi(-24),stoi(9));
  case 47:
  a4 = deg1pol_shallow(gen_1, gen_2, v);
  return mkpoln(9, gen_1,gen_0,gen_0,a4,a4,gen_0,gen_1,gen_2,gen_1);
  case 48:
  a2 = deg1pol_shallow(stoi(-4), stoi(-7), v);
  a1 = deg1pol_shallow(stoi(-4), gen_m1, v);
  return mkpoln(9, gen_1,stoi(-8),stoi(16),stoi(6),stoi(-18),stoi(-18),a2,a1,pol_mx(v));
  default: return NULL;}}

static GEN QT9(long k, long v)
{ GEN a8, a7, a6, a5, a4, a3, a2, a1, a0;
  switch(k) {
  case 1:
  a7 = deg2pol_shallow(stoi(-9), gen_0, stoi(-27), v);
  a5 = gtopoly(mkvecsmall5(27, 0L, 162L, 0L, 243L), v);
  a3 = gtopoly(mkvecsmalln(7, -30L, 0L, -270L, 0L, -810L, 0L, -810L), v);
  a1 = gtopoly(mkvecsmalln(9, 9L, 0L, 108L, 0L, 486L, 0L, 972L, 0L, 729L), v);
  a0 = gtopoly(mkvecsmalln(10, -1L,-9L, 0L,-72L, 54L,-162L, 216L, 0L, 243L, 243L), v);
  return mkpoln(10, gen_1,gen_0,a7,gen_0,a5,gen_0,a3,gen_0,a1,a0);
  case 2:
  a7 = deg2pol_shallow(stoi(-162), stoi(162), stoi(237), v);
  a6 = deg2pol_shallow(stoi(-2916), stoi(2916), stoi(609), v);
  a5 = gtopoly(mkvecsmall5(6561, -13122L, -6075L, 12636L, -774L), v);
  a4 = gtopoly(mkvecsmall5(59049, -118098L, 64719L, -5670L, -1572L), v);
  a3 = gtopoly(mkvecsmall5(-2916L, 5832L, 14364L, -17280L, 584L), v);
  a2 = gtopoly(mkvecsmall5(-26244L, 52488L, -28188L, 1944L, 720L), v);
  a1 = deg2pol_shallow(stoi(-2592), stoi(2592), stoi(-96), v);
  return mkpoln(10, gen_1,stoi(27),a7,a6,a5,a4,a3,a2,a1,stoi(-64));
  case 3:
  a6 = monomial(stoi(-9), 1, v);
  a3 = monomial(stoi(27), 2, v);
  a0 = monomial(stoi(-3), 3, v);
  return mkpoln(10, gen_1, gen_0, gen_0, a6, gen_0, gen_0, a3, gen_0, gen_0, a0);
  case 4:
  a7 = deg1pol_shallow(stoi(-162), stoi(237), v);
  a6 = deg1pol_shallow(stoi(-2916), stoi(609), v);
  a5 = deg2pol_shallow(stoi(6561), stoi(-12636), stoi(-774), v);
  a4 = deg2pol_shallow(stoi(59049), stoi(5670), stoi(-1572), v);
  a3 = deg2pol_shallow(stoi(-2916), stoi(17280), stoi(584), v);
  a2 = deg2pol_shallow(stoi(-26244), stoi(-1944), stoi(720), v);
  a1 = deg1pol_shallow(stoi(-2592), stoi(-96), v);
  return mkpoln(10, gen_1,stoi(27),a7,a6,a5,a4,a3,a2,a1,stoi(-64));
  case 5:
  a6 = monomial(stoi(-6), 1, v);
  a3 = deg2pol_shallow(stoi(-3), stoi(12), stoi(3), v);
  a0 = monomial(stoi(-8), 3, v);
  return mkpoln(10, gen_1, gen_0, gen_0, a6, gen_0, gen_0, a3, gen_0, gen_0, a0);
  case 6:
  a7 = deg2pol_shallow(stoi(-9), gen_0, stoi(-27), v);
  a5 = gtopoly(mkvecsmall5(27, 0L, 162L, 0L, 243L), v);
  a3 = gtopoly(mkvecsmalln(7, -30L, 0L, -270L, 0L, -810L, 0L, -810L), v);
  a1 = gtopoly(mkvecsmalln(9, 9L, 0L, 108L, 0L, 486L, 0L, 972L, 0L, 729L), v);
  a0 = gtopoly(mkvecsmalln(10, -2L, 0L, -24L, 0L, -108L, 0L, -216L, 0L, -162L, 0L), v);
  return mkpoln(10, gen_1, gen_0, a7, gen_0, a5, gen_0, a3, gen_0, a1, a0);
  case 7:
  a7 = gtopoly(mkvecsmalln(7, -4374L, 13122L, -26091L, 30312L, -25713L, 12744L, -4341L), v);
  a6 = gtopoly(mkvecsmalln(9, 13122L,-52488L, 132846L,-214830L, 259842L,-222870L, 143664L,-59286L, 15388L),v);
  a5 = gtopoly(readseq((char*)"[4782969,-28697814,100048689,-237180150,424378629,-590109570,655752879,-582355818,414697131,-230740074,98135199,-28712070,5111388]"),v);
  a4 = gtopoly(readseq((char*)"[-9565938,66961566,-269307180,745342722,-1571360346,2620410768,-3558213774,3973302162,-3676193682,2801629944,-1743622110,861109674,-324660600,84166794,-12391674]"),v);
  a3 = gtopoly(readseq((char*)"[-1549681956,13947137604,-69027808608,236087349840,-616055671332,1287333993708,-2220172450845,3217910657274,-3967837679193,4191222203502,-3807548449710,2975042726178,-1994080593309,1137401229030,-545047479870,213801060294,-65934397221,14507854614,-1884202425]"),v);
  a2 = gtopoly(readseq((char*)"[2179094778,-15253663446,58109194080,-150357539682,289819605474,-434366225748,516445462386,-490296325050,368267017482,-213551288244,89342885898,-22517312706,0,2179094778,-726364926]"),v);
  a1 = gtopoly(readseq((char*)"[353013354036,-3177120186324,15753402515088,-54012495897360,141391291035456,-296571893826096,513499326246144,-746938486164024,923034040633908,-974568179403756,880903422196056,-680171022166104,445976442725184,-245502628608888,111450528785736,-40487580975240,11207810808180,-2139871071996,223720397208]"),v);
  a0 = gtopoly(readseq((char*)"[1107302976080,-9965726784720,49496443030776,-170081737125888,446464559955456,-939435844906272,1632386047337136,-2383801846905024,2958492091490544,-3138318094805936,2851194433108392,-2213720109779136,1460311164854304,-809217014919264,370060654605936,-135533884272192,37869761781936,-7308199642128,775112083256]"),v);
  return mkpoln(10, gen_1, gen_0, a7, a6, a5, a4, a3, a2, a1, a0);
  case 8:
  a7 = deg1pol_shallow(stoi(3), stoi(-9), v);
  a6 = deg1pol_shallow(stoi(-3), stoi(3), v);
  a5 = deg2pol_shallow(stoi(3), stoi(-9), stoi(27), v);
  a4 = deg2pol_shallow(stoi(3), stoi(24), stoi(9), v);
  a3 = gtopoly(mkvecsmall4(1, 0L, 30L,-24L), v);
  a2 = gtopoly(mkvecsmall4(-3L, -15L, -9L, 27L), v);
  a1 = gtopoly(mkvecsmall4(-9L, -24L, -33L, 18L), v);
  a0 = gtopoly(mkvecsmall5(-1L, -7L, -9L, -21L, -26L), v);
  return mkpoln(10, gen_1,gen_0,a7,a6,a5,a4,a3,a2,a1,a0);
  /*case 9:*/
  case 10:
  return mkpoln(10, gen_1,gen_0,gen_0,gen_0,gen_0,gen_0,gen_0,gen_0,gen_0,pol_mx(v));
  case 11:
  a7 = gtopoly(mkvecsmall3(756, 0L, 2223L),v);
  a6 = gtopoly(mkvecsmall5(2241, 0L,-59796L, 0L,-98292L),v);
  a5 = gtopoly(mkvecsmall5(788292, 0L, 2434536L, 0L, 1943055L),v);
  a4 = gtopoly(mkvecsmalln(7, -2221020L, 0L,-11276658L, 0L,-18068184L, 0L,-9662454L),v);
  a3 = gtopoly(mkvecsmalln(9, 1245375L, 0L, 4562892L, 0L,-1829628L, 0L,-17170236L, 0L,-12229791L),v);
  a2 = gtopoly(mkvecsmalln(9, 34007850L, 0L, 84141180L, 0L, 21112569L, 0L,-76385268L, 0L,-47416320L),v);
  a1 = gtopoly(mkvecsmalln(11, -10935000L, 0L,-67290345L, 0L,-165190428L, 0L,-202198032L, 0L,-123391296L, 0L,-30030336L),v);
  a0 = gtopoly(mkvecsmalln(13, -11390625L, 0L,-84564000L, 0L,-260954784L, 0L,-428398848L, 0L,-394557696L, 0L,-193277952L, 0L,-39337984L),v);
  return mkpoln(10, gen_1,stoi(-54),a7,a6,a5,a4,a3,a2,a1,a0);
  case 12:
  a5 = deg1pol_shallow(stoi(3), stoi(36), v);
  a4 = deg1pol_shallow(stoi(-3), stoi(-27), v);
  a3 = deg1pol_shallow(gen_1, stoi(-21), v);
  return mkpoln(10, gen_1,gen_0,stoi(-9),pol_mx(v),a5,a4,a3,stoi(27),stoi(-9),gen_1);
  case 13:
  a6 = monomial(stoi(9), 3, v);
  a0 = monomial(gen_m1, 3, v);
  return mkpoln(10, gen_1,gen_0,gen_0,a6,gen_0,gen_0,gen_m1,gen_0,gen_0,a0);
  /*case 14:*/
  /*case 15:*/
  /*case 16:*/
  case 17:
  a8 = monomial(stoi(-81), 1, v);
  a6 = monomial(stoi(900), 1, v);
  a4 = monomial(stoi(-342), 1, v);
  a2 = monomial(stoi(36), 1, v);
  return mkpoln(10, gen_1,a8,stoi(-84),a6,stoi(102),a4,stoi(-20),a2,gen_1,pol_mx(v));
  case 18:
  return mkpoln(10, gen_1,gen_0,gen_0,gen_0,gen_0,gen_0,pol_x(v),gen_0,gen_0,gen_1);
  case 19:
  a5 = monomial(stoi(6), 1, v);
  a1 = monomial(stoi(-3), 2, v);
  a0 = gsqr(pol_x(v));
  return mkpoln(10, gen_1, stoi(-3), gen_0, gen_0, a5, a5, gen_0, gen_0, a1, a0);
  case 20:
  a7 = deg1pol_shallow(stoi(81), stoi(-3), v);
  a5 = deg1pol_shallow(stoi(-99), stoi(3), v);
  a3 = deg1pol_shallow(stoi(19), gen_m1, v);
  return mkpoln(10, gen_1,gen_0,a7,stoi(-729),a5,stoi(243),a3,stoi(-27),pol_mx(v),gen_1);
  case 21:
  a0 = deg2pol_shallow(stoi(3), stoi(9), gen_0, v);
  return mkpoln(10, gen_1,gen_0,gen_0,gen_0,gen_0,gen_0,a0,gen_0,gen_0,a0);
  case 22:
  a6 = monomial(stoi(9), 1, v);
  return mkpoln(10, gen_1,gen_0,gen_0,a6,gen_0,gen_0,gen_m1,gen_0,gen_0,pol_mx(v));
  /*case 23:*/
  case 24:
  return mkpoln(10, gen_1,gen_0,gen_0,gen_0,gen_0,gen_0,gen_m1,gen_0,gen_0,pol_mx(v));
  case 25:
  a7 = deg1pol_shallow(stoi(9), stoi(3), v);
  a6 = deg1pol_shallow(stoi(-19), gen_m1, v);
  a5 = deg1pol_shallow(stoi(92), stoi(-243), v);
  a4 = deg1pol_shallow(stoi(-100), stoi(297), v);
  a3 = deg1pol_shallow(stoi(19), stoi(-786), v);
  a2 = deg1pol_shallow(gen_m1, stoi(246), v);
  return mkpoln(10, gen_1,stoi(-3),a7,a6,a5,a4,a3,a2,stoi(-27),gen_1);
  case 26:
  return mkpoln(10, gen_1, stoi(-3), gen_0, pol_x(v), stoi(6), stoi(6), pol_mx(v), gen_0, stoi(-3), gen_1);
  /*case 27:*/
  case 28:
  a2 = monomial(stoi(9), 1, v);
  a4 = monomial(stoi(-18), 1, v);
  return mkpoln(10, gen_1,gen_0,stoi(-3),a2,stoi(3),a4,gen_m2,a2,gen_1,pol_mx(v));
  case 29:
  a5 = monomial(stoi(81), 1, v);
  a4 = monomial(stoi(-99), 1, v);
  a3 = deg1pol_shallow(stoi(19), stoi(-729), v);
  a2 = deg1pol_shallow(gen_m1, stoi(243), v);
  return mkpoln(10, gen_1,stoi(-3),stoi(3),gen_m1,a5,a4,a3,a2,stoi(-27),gen_1);
  case 30:
  a3 = deg2pol_shallow(stoi(2187), gen_0, stoi(2916), v);
  a2 = deg2pol_shallow(stoi(-729), gen_0, stoi(-972), v);
  a1 = deg2pol_shallow(stoi(81), gen_0, stoi(108), v);
  a0 = deg2pol_shallow(stoi(-3), gen_0, stoi(-4), v);
  return mkpoln(10, gen_1,stoi(-3),stoi(-24),stoi(56),stoi(-33),stoi(3),a3,a2,a1,a0);
  case 31:
  a3 = deg1pol_shallow(gen_1, gen_m1, v);
  return mkpoln(10, gen_1,gen_0,stoi(-3),gen_0,stoi(3),gen_0,a3,gen_0,pol_mx(v),gen_1);
  case 32:
  a2 = monomial(gen_2, 1, v);
  return mkpoln(10, gen_1, stoi(-3), stoi(4), gen_0, gen_0, gen_0, gen_0, a2, pol_x(v), pol_x(v));
  default: return NULL;}}

static GEN
nfmakeQT(long g, long v)
{
  long deg = g / 100, k = g % 100;
  GEN P;
  switch(deg) {
  case 4: P = QT4(k, v); break;
  case 5: P = QT5(k, v); break;
  case 6: P = QT6(k, v); break;
  case 7: P = QT7(k, v); break;
  case 8: P = QT8(k, v); break;
  case 9: P = QT9(k, v); break;
  default: P = NULL;
  }
  if (!P) pari_err_IMPL(stack_sprintf("group %ldT%ld in nflist / Q(T)", deg,k));
  return P;
}

static GEN
nfmakeAnQT(long n, long v)
{
  GEN A, P = vec_ei(n + 1, 1);
  long s;
  if (odd(n))
  {
    s = (n & 3L) == 1? 1: -1;
    A = sqru(n-2); setsigne(A, s);
    gel(P,2) = monomial(sqru(n), 1, v);
    gel(P,n) = s > 0? gen_1: gen_m1;
    gel(P,n+1) = monomial(A, 1, v);
  }
  else
  {
    s = (n & 3L)? -1 : 1;
    gel(P,2) = utoineg(n);
    gel(P,n+1) = deg2pol_shallow(stoi(s), gen_0, powuu(n-1,n-1), v);
  }
  return RgV_to_RgX_reverse(P, 0);
}

static GEN
nfmakeSnQT(long n, long v)
{
  GEN P = vec_ei(n + 1, 1);
  gel(P,n) = pol_x(v);
  gel(P,n+1) = gen_1; return RgV_to_RgX_reverse(P, 0);
}

GEN
nflistQT(long g, long v)
{
  if (varncmp(0,v) >= 0)
    pari_err(e_MISC, "incorrect variable in nflist / Q(T)");
  if (g > 1000)
  {
    long deg = g / 1000;
    if (deg == 1) return pol_x(0);
    if (deg == 2) return deg2pol_shallow(gen_1, pol_mx(v), gen_1, 0);
    if (g % 1000 == 5) return nfmakeSnQT(deg, v);
    if (g % 1000 == 4) return nfmakeAnQT(deg, v);
  }
  return nfmakeQT(g, v);
}
