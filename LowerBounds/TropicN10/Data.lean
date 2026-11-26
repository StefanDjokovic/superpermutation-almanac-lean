import LowerBounds.TropicSound

namespace SuperpermLowerBounds.Tropic.TropicN10
open SuperpermLowerBounds.Tropic

def tSymInfo : Tree16 (Nat × Nat × Nat) :=
  (.node (.node (.leaf ((0, 0, 0))) (.leaf ((0, 4, 0))) (.leaf ((1, 3, 3))) (.leaf ((2, 3, 1))) (.leaf ((3, 2, 4))) (.leaf ((4, 2, 2))) (.leaf ((5, 2, 0))) (.leaf ((6, 0, 3))) (.leaf ((6, 4, 4)))
  (.leaf ((7, 4, 4))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0)))) (.node (.leaf ((0, 0, 3))) (.leaf ((0, 4, 1))) (.leaf
  ((1, 3, 4))) (.leaf ((2, 3, 2))) (.leaf ((3, 3, 0))) (.leaf ((4, 2, 3))) (.leaf ((5, 2, 1))) (.leaf ((6, 1, 1))) (.leaf ((7, 1, 1))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0)))
  (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0)))) (.node (.leaf ((0, 1, 0))) (.leaf ((0, 4, 2))) (.leaf ((1, 4, 0))) (.leaf ((2, 3, 3))) (.leaf ((3, 3, 1))) (.leaf
  ((4, 2, 4))) (.leaf ((5, 2, 2))) (.leaf ((6, 2, 0))) (.leaf ((7, 2, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0)))
  (.leaf ((0, 0, 0)))) (.node (.leaf ((0, 1, 1))) (.leaf ((0, 4, 3))) (.leaf ((1, 4, 1))) (.leaf ((2, 3, 4))) (.leaf ((3, 3, 2))) (.leaf ((4, 3, 0))) (.leaf ((5, 2, 3))) (.leaf ((6, 2, 1))) (.leaf
  ((7, 2, 1))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0)))) (.node (.leaf ((0, 1, 3))) (.leaf ((0, 4,
  4))) (.leaf ((1, 4, 2))) (.leaf ((2, 4, 0))) (.leaf ((3, 3, 3))) (.leaf ((4, 3, 1))) (.leaf ((5, 2, 4))) (.leaf ((6, 2, 2))) (.leaf ((7, 2, 2))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0,
  0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0)))) (.node (.leaf ((0, 1, 4))) (.leaf ((1, 0, 0))) (.leaf ((1, 4, 3))) (.leaf ((2, 4, 1))) (.leaf ((3, 3, 4)))
  (.leaf ((4, 3, 2))) (.leaf ((5, 3, 0))) (.leaf ((6, 2, 3))) (.leaf ((7, 2, 3))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0,
  0))) (.leaf ((0, 0, 0)))) (.node (.leaf ((0, 2, 0))) (.leaf ((1, 0, 3))) (.leaf ((1, 4, 4))) (.leaf ((2, 4, 2))) (.leaf ((3, 4, 0))) (.leaf ((4, 3, 3))) (.leaf ((5, 3, 1))) (.leaf ((6, 2, 4)))
  (.leaf ((7, 2, 4))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0)))) (.node (.leaf ((0, 2, 1))) (.leaf
  ((1, 1, 1))) (.leaf ((2, 0, 0))) (.leaf ((2, 4, 3))) (.leaf ((3, 4, 1))) (.leaf ((4, 3, 4))) (.leaf ((5, 3, 2))) (.leaf ((6, 3, 0))) (.leaf ((7, 3, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0)))
  (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0)))) (.node (.leaf ((0, 2, 2))) (.leaf ((1, 2, 0))) (.leaf ((2, 0, 3))) (.leaf ((2, 4, 4))) (.leaf
  ((3, 4, 2))) (.leaf ((4, 4, 0))) (.leaf ((5, 3, 3))) (.leaf ((6, 3, 1))) (.leaf ((7, 3, 1))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0)))
  (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0)))) (.node (.leaf ((0, 2, 3))) (.leaf ((1, 2, 1))) (.leaf ((2, 1, 1))) (.leaf ((3, 0, 0))) (.leaf ((3, 4, 3))) (.leaf ((4, 4, 1))) (.leaf ((5, 3, 4))) (.leaf
  ((6, 3, 2))) (.leaf ((7, 3, 2))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0)))) (.node (.leaf ((0, 2,
  4))) (.leaf ((1, 2, 2))) (.leaf ((2, 2, 0))) (.leaf ((3, 0, 3))) (.leaf ((3, 4, 4))) (.leaf ((4, 4, 2))) (.leaf ((5, 4, 0))) (.leaf ((6, 3, 3))) (.leaf ((7, 3, 3))) (.leaf ((0, 0, 0))) (.leaf ((0,
  0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0)))) (.node (.leaf ((0, 3, 0))) (.leaf ((1, 2, 3))) (.leaf ((2, 2, 1))) (.leaf ((3, 1, 1)))
  (.leaf ((4, 0, 0))) (.leaf ((4, 4, 3))) (.leaf ((5, 4, 1))) (.leaf ((6, 3, 4))) (.leaf ((7, 3, 4))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0,
  0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0)))) (.node (.leaf ((0, 3, 1))) (.leaf ((1, 2, 4))) (.leaf ((2, 2, 2))) (.leaf ((3, 2, 0))) (.leaf ((4, 0, 3))) (.leaf ((4, 4, 4))) (.leaf ((5, 4, 2)))
  (.leaf ((6, 4, 0))) (.leaf ((7, 4, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0)))) (.node (.leaf
  ((0, 3, 2))) (.leaf ((1, 3, 0))) (.leaf ((2, 2, 3))) (.leaf ((3, 2, 1))) (.leaf ((4, 1, 1))) (.leaf ((5, 0, 0))) (.leaf ((5, 4, 3))) (.leaf ((6, 4, 1))) (.leaf ((7, 4, 1))) (.leaf ((0, 0, 0)))
  (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0)))) (.node (.leaf ((0, 3, 3))) (.leaf ((1, 3, 1))) (.leaf ((2, 2, 4))) (.leaf
  ((3, 2, 2))) (.leaf ((4, 2, 0))) (.leaf ((5, 0, 3))) (.leaf ((5, 4, 4))) (.leaf ((6, 4, 2))) (.leaf ((7, 4, 2))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0)))
  (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0)))) (.node (.leaf ((0, 3, 4))) (.leaf ((1, 3, 2))) (.leaf ((2, 3, 0))) (.leaf ((3, 2, 3))) (.leaf ((4, 2, 1))) (.leaf ((5, 1, 1))) (.leaf
  ((6, 0, 0))) (.leaf ((6, 4, 3))) (.leaf ((7, 4, 3))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0))) (.leaf ((0, 0, 0)))))

def tSymId : Tree16 (Option Nat) :=
  (.node (.node (.leaf (some 0)) (.leaf (some 12)) (.leaf (none)) (.leaf (some 37)) (.leaf (some 46)) (.leaf (none)) (.leaf (some 71)) (.leaf (some 80)) (.leaf (some 94)) (.leaf (some 105)) (.leaf
  (some 114)) (.leaf (none)) (.leaf (some 137)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none)) (.leaf (some 13)) (.leaf (none)) (.leaf (some 38)) (.leaf (some 47)) (.leaf (some
  59)) (.leaf (some 72)) (.leaf (some 81)) (.leaf (none)) (.leaf (some 106)) (.leaf (some 115)) (.leaf (none)) (.leaf (some 138)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none))
  (.leaf (some 14)) (.leaf (none)) (.leaf (some 39)) (.leaf (some 48)) (.leaf (none)) (.leaf (some 73)) (.leaf (some 82)) (.leaf (none)) (.leaf (some 107)) (.leaf (some 116)) (.leaf (none)) (.leaf
  (some 139)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some 1)) (.leaf (some 15)) (.leaf (some 24)) (.leaf (none)) (.leaf (some 49)) (.leaf (none)) (.leaf (some 74)) (.leaf (some
  83)) (.leaf (some 95)) (.leaf (some 108)) (.leaf (some 117)) (.leaf (none)) (.leaf (some 140)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none)) (.leaf (some 16)) (.leaf (some 25))
  (.leaf (none)) (.leaf (some 50)) (.leaf (none)) (.leaf (some 75)) (.leaf (some 84)) (.leaf (none)) (.leaf (some 109)) (.leaf (some 118)) (.leaf (none)) (.leaf (some 141)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.node (.leaf (some 2)) (.leaf (some 17)) (.leaf (some 26)) (.leaf (some 40)) (.leaf (some 51)) (.leaf (some 60)) (.leaf (none)) (.leaf (some 85)) (.leaf (none)) (.leaf (some
  110)) (.leaf (some 119)) (.leaf (some 129)) (.leaf (some 142)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some 3)) (.leaf (some 18)) (.leaf (some 27)) (.leaf (none)) (.leaf (some
  52)) (.leaf (some 61)) (.leaf (none)) (.leaf (some 86)) (.leaf (none)) (.leaf (some 111)) (.leaf (some 120)) (.leaf (none)) (.leaf (some 143)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node
  (.leaf (none)) (.leaf (some 19)) (.leaf (some 28)) (.leaf (none)) (.leaf (some 53)) (.leaf (some 62)) (.leaf (some 76)) (.leaf (some 87)) (.leaf (some 96)) (.leaf (none)) (.leaf (some 121)) (.leaf
  (none)) (.leaf (some 144)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some 4)) (.leaf (some 20)) (.leaf (some 29)) (.leaf (some 41)) (.leaf (some 54)) (.leaf (some 63)) (.leaf
  (none)) (.leaf (some 88)) (.leaf (some 97)) (.leaf (none)) (.leaf (some 122)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some 5)) (.leaf (some 21))
  (.leaf (some 30)) (.leaf (none)) (.leaf (some 55)) (.leaf (some 64)) (.leaf (none)) (.leaf (some 89)) (.leaf (some 98)) (.leaf (some 112)) (.leaf (some 123)) (.leaf (some 130)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some 6)) (.leaf (none)) (.leaf (some 31)) (.leaf (none)) (.leaf (some 56)) (.leaf (some 65)) (.leaf (some 77)) (.leaf (some 90)) (.leaf (some
  99)) (.leaf (none)) (.leaf (some 124)) (.leaf (some 131)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some 7)) (.leaf (none)) (.leaf (some 32)) (.leaf (none)) (.leaf
  (some 57)) (.leaf (some 66)) (.leaf (none)) (.leaf (some 91)) (.leaf (some 100)) (.leaf (none)) (.leaf (some 125)) (.leaf (some 132)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.node (.leaf (some 8)) (.leaf (some 22)) (.leaf (some 33)) (.leaf (some 42)) (.leaf (none)) (.leaf (some 67)) (.leaf (none)) (.leaf (some 92)) (.leaf (some 101)) (.leaf (some 113)) (.leaf (some
  126)) (.leaf (some 133)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some 9)) (.leaf (none)) (.leaf (some 34)) (.leaf (some 43)) (.leaf (none)) (.leaf (some 68))
  (.leaf (none)) (.leaf (some 93)) (.leaf (some 102)) (.leaf (none)) (.leaf (some 127)) (.leaf (some 134)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some 10)) (.leaf
  (none)) (.leaf (some 35)) (.leaf (some 44)) (.leaf (some 58)) (.leaf (some 69)) (.leaf (some 78)) (.leaf (none)) (.leaf (some 103)) (.leaf (none)) (.leaf (some 128)) (.leaf (some 135)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some 11)) (.leaf (some 23)) (.leaf (some 36)) (.leaf (some 45)) (.leaf (none)) (.leaf (some 70)) (.leaf (some 79)) (.leaf (none))
  (.leaf (some 104)) (.leaf (none)) (.leaf (none)) (.leaf (some 136)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))

def tD1State : Tree16 Nat :=
  (.node (.node (.leaf (1)) (.leaf (17)) (.leaf (33)) (.leaf (49)) (.leaf (65)) (.leaf (81)) (.leaf (97)) (.leaf (113)) (.leaf (129)) (.leaf (145)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (2)) (.leaf (18)) (.leaf (34)) (.leaf (50)) (.leaf (66)) (.leaf (82)) (.leaf (98)) (.leaf (114)) (.leaf (130)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (3)) (.leaf (19)) (.leaf (35)) (.leaf (51)) (.leaf (67)) (.leaf (83)) (.leaf (99)) (.leaf (115)) (.leaf (131)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (4)) (.leaf (20)) (.leaf (36)) (.leaf (52)) (.leaf (68)) (.leaf (84)) (.leaf (100)) (.leaf (116)) (.leaf (132)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (5)) (.leaf (21)) (.leaf (37)) (.leaf (53)) (.leaf (69)) (.leaf (85)) (.leaf (101)) (.leaf (117)) (.leaf (133)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (6)) (.leaf (22)) (.leaf (38)) (.leaf (54)) (.leaf (70)) (.leaf (86)) (.leaf (102)) (.leaf (118)) (.leaf (134))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (7)) (.leaf (23)) (.leaf (39)) (.leaf (55)) (.leaf (71)) (.leaf (87)) (.leaf (103)) (.leaf (119))
  (.leaf (135)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (8)) (.leaf (24)) (.leaf (40)) (.leaf (56)) (.leaf (72)) (.leaf (88)) (.leaf (104))
  (.leaf (120)) (.leaf (136)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (9)) (.leaf (25)) (.leaf (41)) (.leaf (57)) (.leaf (73)) (.leaf (89))
  (.leaf (105)) (.leaf (121)) (.leaf (137)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (10)) (.leaf (26)) (.leaf (42)) (.leaf (58)) (.leaf (74))
  (.leaf (90)) (.leaf (106)) (.leaf (122)) (.leaf (138)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (11)) (.leaf (27)) (.leaf (43)) (.leaf (59))
  (.leaf (75)) (.leaf (91)) (.leaf (107)) (.leaf (123)) (.leaf (139)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (12)) (.leaf (28)) (.leaf (44))
  (.leaf (60)) (.leaf (76)) (.leaf (92)) (.leaf (108)) (.leaf (124)) (.leaf (140)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (13)) (.leaf (29))
  (.leaf (45)) (.leaf (61)) (.leaf (77)) (.leaf (93)) (.leaf (109)) (.leaf (125)) (.leaf (141)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (14))
  (.leaf (30)) (.leaf (46)) (.leaf (62)) (.leaf (78)) (.leaf (94)) (.leaf (110)) (.leaf (126)) (.leaf (142)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (15)) (.leaf (31)) (.leaf (47)) (.leaf (63)) (.leaf (79)) (.leaf (95)) (.leaf (111)) (.leaf (127)) (.leaf (143)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (16)) (.leaf (32)) (.leaf (48)) (.leaf (64)) (.leaf (80)) (.leaf (96)) (.leaf (112)) (.leaf (128)) (.leaf (144)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))))

def tMaxPsi0 : Tree16 (Option Int) :=
  (.node (.node (.leaf (some (-22))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (-45))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-22))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none))
  (.leaf (some (-16))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none)) (.leaf (some (-16))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none)) (.leaf (none)) (.leaf (some (-8))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none)) (.leaf (none))
  (.leaf (some (-8))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some 0)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some 0)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (some 8)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some 8)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some 16)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some 16)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (-45))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))))

def tMaxPsi1 : Tree16 (Option Int) :=
  (.node (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (-3))) (.leaf (some (-64))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-19))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-19))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))) (.node (.leaf (some (-19))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-19))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (some (-43))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (some (-35))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (-27))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (-19))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (-11))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))

def tMaxPsi2 : Tree16 (Option Int) :=
  (.node (.node (.leaf (none)) (.leaf (some (-100))) (.leaf (some (-95))) (.leaf (some (-89))) (.leaf (some (-54))) (.leaf (some (-46))) (.leaf (some (-38))) (.leaf (none)) (.leaf (some (-84))) (.leaf
  (some (-145))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none)) (.leaf (some (-100))) (.leaf (some (-95))) (.leaf (some (-89))) (.leaf
  (some (-81))) (.leaf (some (-46))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node
  (.leaf (some (-49))) (.leaf (some (-100))) (.leaf (some (-122))) (.leaf (some (-89))) (.leaf (some (-81))) (.leaf (some (-46))) (.leaf (some (-38))) (.leaf (some (-30))) (.leaf (some (-91))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-49))) (.leaf (some (-100))) (.leaf (some (-122))) (.leaf (some (-89))) (.leaf
  (some (-81))) (.leaf (some (-73))) (.leaf (some (-38))) (.leaf (some (-30))) (.leaf (some (-91))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))) (.node (.leaf (some (-49))) (.leaf (some (-100))) (.leaf (some (-124))) (.leaf (some (-116))) (.leaf (some (-81))) (.leaf (some (-73))) (.leaf (some (-40))) (.leaf (some (-30))) (.leaf
  (some (-91))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-49))) (.leaf (none)) (.leaf (some (-122))) (.leaf (some
  (-116))) (.leaf (some (-81))) (.leaf (some (-73))) (.leaf (some (-65))) (.leaf (some (-30))) (.leaf (some (-91))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.node (.leaf (some (-46))) (.leaf (none)) (.leaf (some (-122))) (.leaf (some (-116))) (.leaf (some (-108))) (.leaf (some (-73))) (.leaf (some (-65))) (.leaf (some (-32)))
  (.leaf (some (-91))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-46))) (.leaf (none)) (.leaf (none)) (.leaf (some
  (-116))) (.leaf (some (-108))) (.leaf (some (-73))) (.leaf (some (-65))) (.leaf (some (-57))) (.leaf (some (-118))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.node (.leaf (some (-46))) (.leaf (some (-70))) (.leaf (none)) (.leaf (some (-116))) (.leaf (some (-108))) (.leaf (some (-100))) (.leaf (some (-65))) (.leaf (some (-57)))
  (.leaf (some (-118))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-46))) (.leaf (some (-70))) (.leaf (none)) (.leaf
  (none)) (.leaf (some (-108))) (.leaf (some (-100))) (.leaf (some (-65))) (.leaf (some (-57))) (.leaf (some (-118))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.node (.leaf (some (-46))) (.leaf (some (-70))) (.leaf (some (-62))) (.leaf (none)) (.leaf (some (-108))) (.leaf (some (-100))) (.leaf (some (-92))) (.leaf (some (-57)))
  (.leaf (some (-118))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-73))) (.leaf (some (-70))) (.leaf (some (-62)))
  (.leaf (none)) (.leaf (none)) (.leaf (some (-100))) (.leaf (some (-92))) (.leaf (some (-57))) (.leaf (some (-118))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.node (.leaf (some (-73))) (.leaf (some (-70))) (.leaf (some (-62))) (.leaf (some (-54))) (.leaf (none)) (.leaf (some (-100))) (.leaf (some (-92))) (.leaf (some (-84)))
  (.leaf (some (-145))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-73))) (.leaf (some (-95))) (.leaf (some (-62)))
  (.leaf (some (-54))) (.leaf (none)) (.leaf (none)) (.leaf (some (-92))) (.leaf (some (-84))) (.leaf (some (-145))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.node (.leaf (some (-73))) (.leaf (some (-97))) (.leaf (some (-62))) (.leaf (some (-54))) (.leaf (some (-46))) (.leaf (none)) (.leaf (some (-92))) (.leaf (some (-84)))
  (.leaf (some (-145))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-73))) (.leaf (some (-95))) (.leaf (some (-89)))
  (.leaf (some (-54))) (.leaf (some (-46))) (.leaf (none)) (.leaf (none)) (.leaf (some (-84))) (.leaf (some (-145))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))))

def tCegar : Tree16 (List Nat) :=
  (.node (.node (.leaf ([118, 118, 118, 118, 118, 118])) (.leaf ([118, 118, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118,
  118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 118])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([]))
  (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([]))) (.node (.leaf ([100, 118, 118, 118, 118, 118, 100])) (.leaf ([100, 118, 118, 118, 100, 118, 118, 118, 118, 100, 118,
  118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 118, 118])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf
  ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([]))) (.node (.leaf ([118, 118, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 118, 118])) (.leaf ([118, 118, 118,
  100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 118, 100, 118, 118,
  118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf
  ([])) (.leaf ([])) (.leaf ([])) (.leaf ([]))) (.node (.leaf ([100, 118, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 118, 118])) (.leaf ([118, 100, 118, 118, 118, 100, 118, 118, 118, 100]))
  (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([]))) (.node (.leaf
  ([100, 118, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 118, 100])) (.leaf ([118, 118, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118,
  118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 118, 118])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([]))
  (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([]))) (.node (.leaf ([100, 118, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 118, 118]))
  (.leaf ([100, 118, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 118,
  118])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([]))) (.node
  (.leaf ([118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 118, 118, 100, 118])) (.leaf ([118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118,
  118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100,
  118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf
  ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([]))) (.node (.leaf ([100, 118, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118,
  118, 118, 118, 100, 118, 118, 118, 100])) (.leaf ([100, 118, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100,
  118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 118])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([]))
  (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([]))) (.node (.leaf ([118, 118, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 118, 100])) (.leaf ([118, 118, 118, 118, 100, 118, 118,
  118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118,
  118, 118, 118, 100, 118, 118, 118])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([]))
  (.leaf ([])) (.leaf ([]))) (.node (.leaf ([118, 118, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 118, 118])) (.leaf ([100, 118, 118, 118, 100, 118, 118,
  118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118,
  118, 118, 118, 100, 118, 118, 118])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([]))
  (.leaf ([])) (.leaf ([]))) (.node (.leaf ([100, 118, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 118, 100]))
  (.leaf ([118, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118,
  118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([]))
  (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([]))) (.node (.leaf ([118, 118, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118,
  118, 100])) (.leaf ([118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118,
  100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 100])) (.leaf
  ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([]))) (.node (.leaf ([118,
  118, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 118, 100])) (.leaf ([118, 100, 118, 118, 118, 100, 118, 118,
  118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 100, 118, 118, 118, 118, 100])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([]))
  (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([]))) (.node (.leaf ([100, 118, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118,
  118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 118, 100])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([]))
  (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([]))) (.node (.leaf ([118, 118, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100,
  118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 118, 118])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf
  ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([]))) (.node (.leaf ([118, 118, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118,
  118, 100, 118, 118, 118, 118, 100, 118, 118, 100, 118, 118, 118, 118, 100, 118, 118, 118, 100])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf
  ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([])) (.leaf ([]))))

def tPairMode : Tree16 (Tree16 Nat) :=
  (.node (.node (.leaf ((.node (.node (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.leaf (0)))) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0))) (.node (.leaf ((.node (.node
  (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.leaf (0)))) (.leaf
  ((.leaf (0)))) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0))) (.node (.leaf ((.node (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.leaf (0))))
  (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf
  (.leaf 0))) (.node (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.leaf (0)))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0))
  (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0))) (.node (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf
  ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.leaf (0)))) (.leaf ((.leaf (0)))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (2)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf
  (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0))) (.node (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (1))
  (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (1)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.leaf (0)))) (.leaf ((.leaf (0)))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf
  0)) (.leaf (.leaf 0))) (.node (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (1)) (.leaf (0)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (0)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.leaf (0)))) (.leaf ((.leaf (0)))) (.leaf ((.leaf (0)))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (2)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (2)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf (.leaf 0))
  (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0))) (.node (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.leaf (0)))) (.leaf ((.node (.node (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.leaf (0)))) (.leaf
  ((.leaf (0)))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.leaf (0)))) (.leaf (.leaf 0))
  (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0))) (.node (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (1)) (.leaf (0)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (0)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.leaf (0)))) (.leaf ((.leaf (0)))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.leaf (0)))) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)))
  (.node (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.leaf (0)))) (.leaf ((.node (.node (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.leaf (0)))) (.leaf
  ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.leaf (0)))) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf
  (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0))) (.node (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.leaf (0)))) (.leaf ((.node (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf
  ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.leaf (0)))) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0))
  (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0))) (.node (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)))))) (.leaf ((.leaf (0)))) (.leaf ((.node (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.leaf (0)))) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0))
  (.leaf (.leaf 0)) (.leaf (.leaf 0))) (.node (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.leaf (0)))) (.leaf (.leaf 0)) (.leaf (.leaf 0))
  (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0))) (.node (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.leaf (0)))) (.leaf ((.node (.node
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.leaf (0)))) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0))
  (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0))) (.node (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf
  ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1))
  (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf
  (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.leaf (0))))
  (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0))) (.node (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf
  ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.leaf (0)))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.node (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (1)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))) (.leaf ((.leaf (0)))) (.leaf (.leaf 0))
  (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0)) (.leaf (.leaf 0))))

def tStD0 : Tree16 Bool :=
  (.node (.node (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.node (.leaf (true)) (.leaf (false)) (.leaf (false)) (.leaf (false))
  (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)))
  (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false))) (.node (.node (.leaf (true)) (.leaf (false)) (.leaf (false)) (.leaf
  (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf
  (false))) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.node (.leaf (true)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf
  (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false))) (.leaf (false)) (.leaf
  (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false))) (.node (.node (.leaf (true)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false))
  (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false))) (.leaf (false))
  (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf
  (false)) (.leaf (false))) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.node (.leaf (false)) (.node (.leaf (true)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false))
  (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false))) (.leaf (false)) (.leaf (false))
  (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)))
  (.node (.leaf (false)) (.node (.leaf (true)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf
  (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false))) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf
  (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false))) (.node (.leaf (false)) (.leaf (false)) (.node (.leaf (true)) (.leaf (false))
  (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf
  (false)) (.leaf (false))) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf
  (false)) (.leaf (false)) (.leaf (false))) (.node (.leaf (false)) (.leaf (false)) (.node (.leaf (true)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false))
  (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false))) (.leaf (false)) (.leaf (false)) (.leaf (false))
  (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false))) (.node (.leaf (false)) (.leaf
  (false)) (.leaf (false)) (.node (.leaf (true)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf
  (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false))) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf
  (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false))) (.node (.leaf (false)) (.leaf (false)) (.leaf (false)) (.node (.leaf (true)) (.leaf (false)) (.leaf (false))
  (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf
  (false))) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf
  (false))) (.node (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.node (.leaf (true)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false))
  (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false))) (.leaf (false)) (.leaf (false)) (.leaf (false))
  (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false))) (.node (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf
  (false)) (.node (.leaf (true)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf
  (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false))) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf
  (false)) (.leaf (false)) (.leaf (false)) (.leaf (false))) (.node (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.node (.leaf (true)) (.leaf (false)) (.leaf (false))
  (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf
  (false))) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false))) (.node (.leaf (false))
  (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.node (.leaf (true)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false))
  (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false))) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false))
  (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false)) (.leaf (false))))

def tStPar : Tree16 Nat :=
  (.node (.node (.node (.leaf (0)) (.leaf (250)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (265)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (282)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (298)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (312)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (331)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (347)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (362)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (379)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (395)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (154)) (.leaf (411)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (170)) (.leaf (427)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (185)) (.leaf (445)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (201)) (.leaf (462)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (217)) (.leaf (478)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (234)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))) (.node (.node (.leaf (0)) (.leaf (251)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (266)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (283)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (299)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (313)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (332)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (348)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (364)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (380))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (396)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (155))
  (.leaf (412)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (171)) (.leaf (428)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (186)) (.leaf (446)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (202)) (.leaf (463)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (218)) (.leaf (479)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (235)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)))) (.node (.node (.leaf (0)) (.leaf (252)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (267)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (284)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (300)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (315)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (333)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (349)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (365)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (381)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (101)) (.leaf (397)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (156)) (.leaf (413)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (172)) (.leaf (429)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (187)) (.leaf (447)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (203)) (.leaf (464)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (219)) (.leaf (480)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (236)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))) (.node (.node (.leaf (0)) (.leaf (253)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (268)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (285)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (301)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (316)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (334)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (350))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (366)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (382)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (119)) (.leaf (398)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (157)) (.leaf (414)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (173)) (.leaf (430)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (188)) (.leaf (449)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (204)) (.leaf (465)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (221)) (.leaf (482)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (237)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)))) (.node (.node (.leaf (0)) (.leaf (254)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (269)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (286)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (302)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (317)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (335)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (351)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (367)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (383)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (119)) (.leaf (399)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (157)) (.leaf (415)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (174)) (.leaf (430)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (189)) (.leaf (450)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (205)) (.leaf (466)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (222)) (.leaf (483)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (238)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))) (.node (.node (.leaf (0)) (.leaf (255)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (271)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (287)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (303)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (318))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (336)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (352)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (368)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (384)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (146)) (.leaf (400)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (158)) (.leaf (416)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (175)) (.leaf (431)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (190)) (.leaf (451)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (205)) (.leaf (467)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (223)) (.leaf (484)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (239)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))) (.node (.node (.leaf (0)) (.leaf (256)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (272)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (288)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (304)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (319)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (337)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (352)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (369)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (385)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (147)) (.leaf (401)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (159)) (.leaf (417)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (176)) (.leaf (432)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (191)) (.leaf (452)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (206)) (.leaf (468)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (224)) (.leaf (485)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (240)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))) (.node (.node (.leaf (0)) (.leaf (257)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (273)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (289))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (305)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (321)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (338)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (353)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (370)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (386)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (148)) (.leaf (402)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (160)) (.leaf (418)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (176)) (.leaf (433)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (192)) (.leaf (453)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (207)) (.leaf (469)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (225)) (.leaf (486)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (241)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))) (.node (.node (.leaf (0)) (.leaf (257)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (274)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (290)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (306)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (323)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (339)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (354)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (371)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (387)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (148)) (.leaf (403)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (161)) (.leaf (419)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (177)) (.leaf (435)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (193)) (.leaf (454)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (208)) (.leaf (470)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (226)) (.leaf (487)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (242)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))) (.node (.node (.leaf (0)) (.leaf (258))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf
  (275)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0))
  (.leaf (291)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (307)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (324)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (340)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (355)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (372)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (388)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (149)) (.leaf (404)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (162)) (.leaf (420)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (178)) (.leaf (436)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (194)) (.leaf (455)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (209)) (.leaf (471)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (227)) (.leaf (488)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (243)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))) (.node (.node (.leaf (0)) (.leaf (259)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (276)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (292)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (307)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (325)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (341)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (356)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (373)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (389)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (150)) (.leaf (405)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (163)) (.leaf (421)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (179)) (.leaf (437)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (195)) (.leaf (456)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (210)) (.leaf (472)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (228)) (.leaf (489)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (244)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))) (.node (.node (.leaf (0))
  (.leaf (260)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (0)) (.leaf (277)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (0)) (.leaf (293)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (308)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (326)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (342)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (356)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (374)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (390)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (151)) (.leaf (406)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (165)) (.leaf (422)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (180)) (.leaf (438)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (196)) (.leaf (457)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (211)) (.leaf (473)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (229)) (.leaf (490)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (245)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))) (.node (.node (.leaf (0)) (.leaf (261)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (278)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (294)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (309)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (327)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (343)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (357)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (375)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (391)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (152)) (.leaf (407)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (167)) (.leaf (423)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (181)) (.leaf (440)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (197)) (.leaf (458)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (211)) (.leaf (474))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (230)) (.leaf
  (491)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (246))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))) (.node (.node
  (.leaf (0)) (.leaf (262)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (0)) (.leaf (279)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (0)) (.leaf (295)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (310)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (328)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (344)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (359)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (376)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (392)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (152)) (.leaf (408)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (168)) (.leaf (424)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (182)) (.leaf (442)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (198)) (.leaf (459)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (212)) (.leaf (475)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (231)) (.leaf (492)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (247)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))) (.node (.node (.leaf (0)) (.leaf (262)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (280)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (296)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (311)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (329)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (345)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (360)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (377)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (393)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (153)) (.leaf (409)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (169)) (.leaf (425)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (183)) (.leaf (443))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (199)) (.leaf
  (460)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (214))
  (.leaf (476)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (232)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (248)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))))
  (.node (.node (.leaf (0)) (.leaf (263)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (0)) (.leaf (281)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (297)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (312)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (330)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (346)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (361)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (378)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (0)) (.leaf (394)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (153)) (.leaf (410)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (169)) (.leaf (426)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (184)) (.leaf (444)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (200)) (.leaf (461)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (216)) (.leaf (477)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (233)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (249)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))

def tStSym : Tree16 Nat :=
  (.node (.node (.node (.leaf (0)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (15)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (31)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (47)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (63)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (79)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (95)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (111)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (127)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (143)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (100)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))) (.node (.node (.leaf (0)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (16)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (32)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (48)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (64)) (.leaf (118)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (80)) (.leaf (118)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (96)) (.leaf (100)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (112)) (.leaf (118)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (128)) (.leaf (118))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (144)) (.leaf
  (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118))
  (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (100)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)))) (.node (.node (.leaf (1)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (17)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (33)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (49)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (65)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (81)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (97)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (113)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (129)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (100)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))) (.node (.node (.leaf (2)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (18)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (34)) (.leaf (118)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (50)) (.leaf (118)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (66)) (.leaf (118)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (82)) (.leaf (100)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (98)) (.leaf (100))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (114)) (.leaf
  (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (130))
  (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (100)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (100)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (100)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (118)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)))) (.node (.node (.leaf (3)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (19)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (35)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (51)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (67)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (83)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (99)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (115)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (131)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (100)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))) (.node (.node (.leaf (4)) (.leaf (100)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (20)) (.leaf (118)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (36)) (.leaf (118)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (52)) (.leaf (100)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (68)) (.leaf (118))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (84)) (.leaf
  (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (100))
  (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (116)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (132)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (118)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (118)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (100)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (100)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))) (.node (.node (.leaf (5)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (21)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (37)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (53)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (69)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (85)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (101)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (117)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (133)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (100)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))) (.node (.node (.leaf (6)) (.leaf (100)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (22)) (.leaf (100)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (38)) (.leaf (100))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (54)) (.leaf
  (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (70))
  (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (86)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (102)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (118)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (134)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (100)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (100)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (100)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (100)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))) (.node (.node (.leaf (7)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (23)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (39)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (55)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (71)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (87)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (103)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (119)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (135)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))) (.node (.node (.leaf (8)) (.leaf (118))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (24)) (.leaf
  (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (40))
  (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (56)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (72)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (88)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (104)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (120)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (136)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))) (.node (.node (.leaf (9)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (25)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (41)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (57)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (73)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (89)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (105)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (121)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (137)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (100)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (100)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (100)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))) (.node (.node (.leaf (10))
  (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (26)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (42)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (58)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (74)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (90)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (106)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (122)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (138)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (100)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))) (.node (.node (.leaf (11)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (27)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (43)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (59)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (75)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (91)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (107)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (123)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (139)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (100)) (.leaf (118)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (100)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (100)) (.leaf (118)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf
  (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (100))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))) (.node (.node
  (.leaf (12)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))
  (.node (.leaf (28)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0))) (.node (.leaf (44)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (60)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (76)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (92)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (108)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (124)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (140)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))) (.node (.node (.leaf (13)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (29)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (45)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (61)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (77)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (93)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (109)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (125)) (.leaf (100)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (141)) (.leaf (118)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (100)) (.leaf (118)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (100)) (.leaf (118)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf
  (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (100))
  (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf
  (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node
  (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))))
  (.node (.node (.leaf (14)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0))) (.node (.leaf (30)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0))) (.node (.leaf (46)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0))) (.node (.leaf (62)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (78)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (94)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (110)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (126)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (142)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (100)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (100)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))
  (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0))) (.node (.leaf (118)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf
  (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)) (.leaf (0)))))

def tStPsi0 : Tree16 (Option Int) :=
  (.node (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (some (-45))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.node (.leaf (some (-22))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (some (-45))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.node (.leaf (some (-22))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node
  (.leaf (none)) (.node (.leaf (some (-16))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none)) (.node (.leaf (some (-16))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node
  (.leaf (none)) (.leaf (none)) (.node (.leaf (some (-8))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none)) (.leaf (none)) (.node (.leaf (some (-8))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (some 0)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (some 0)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (some 8)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (some 8)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (some 16)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (some 16)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))

def tStPsi1 : Tree16 (Option Int) :=
  (.node (.node (.node (.leaf (some 0)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (some (-11))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (some (-3))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-64))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.node (.leaf (some (-19))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.node (.node (.leaf (some (-19))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.node (.leaf (some (-19))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.node (.node (.leaf (some (-19))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.node (.leaf (some (-43))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.node (.leaf (some (-35))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.node (.leaf (some (-27))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (some (-19))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)))

def tStPsi2 : Tree16 (Option Int) :=
  (.node (.node (.node (.leaf (some (-101))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-73))) (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-95))) (.leaf (some (-36)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))) (.node (.leaf (some (-89))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-54))) (.leaf (some (-34))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-46))) (.leaf (some
  (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.node (.leaf (none)) (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none)) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-84))) (.leaf (some (-40)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))) (.node (.leaf (some (-145))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-38))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-38))) (.leaf (some
  (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.node (.leaf (some (-34))) (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-42))) (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-42))) (.leaf
  (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))) (.node (.node (.leaf (none)) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-100))) (.leaf
  (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-95))) (.leaf (some (-34))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-89))) (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-54)))
  (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-46))) (.leaf (some (-34))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-38))) (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none))
  (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-84))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-145))) (.leaf (some (-44))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some
  (-40))) (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-40))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-38))) (.leaf (some (-36))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf
  (some (-46))) (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-38))) (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))) (.node (.node
  (.leaf (none)) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-100))) (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-95))) (.leaf (some (-36))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node
  (.leaf (some (-89))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-81))) (.leaf (some (-34))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-46))) (.leaf (some (-40))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node
  (.leaf (some (-38))) (.leaf (some (-46))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none)) (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none)) (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some
  (-44))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-44))) (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-38))) (.leaf (some (-36))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf
  (some (-38))) (.leaf (some (-34))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-42))) (.leaf (some (-34))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-40))) (.leaf (some (-34))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node
  (.leaf (some (-44))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))) (.node (.node (.leaf (some (-49))) (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-100))) (.leaf (some (-38))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.node (.leaf (some (-122))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-89))) (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-81))) (.leaf (some (-38))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))) (.node (.leaf (some (-46))) (.leaf (some (-44))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-38))) (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-30))) (.leaf (some (-40)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))) (.node (.leaf (some (-91))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-44))) (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-42))) (.leaf (some
  (-34))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.node (.leaf (some (-42))) (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-42))) (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-36))) (.leaf
  (some (-34))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-42))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))) (.node (.node (.leaf (some (-49)))
  (.leaf (some (-46))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-100))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-122))) (.leaf (some (-44))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some
  (-89))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-81))) (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-73))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf
  (some (-38))) (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-30))) (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-91))) (.leaf (some (-40))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node
  (.leaf (some (-42))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-36))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-42))) (.leaf (some (-34))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node
  (.leaf (some (-40))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-46))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-40))) (.leaf (some (-38))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node
  (.leaf (some (-34))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))) (.node (.node (.leaf (some (-49))) (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-100))) (.leaf (some (-42))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.node (.leaf (some (-124))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-116))) (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-81))) (.leaf (some (-38))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))) (.node (.leaf (some (-73))) (.leaf (some (-34))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-46))) (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-30))) (.leaf (some (-38)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))) (.node (.leaf (some (-91))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-42))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-44))) (.leaf (some
  (-44))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.node (.leaf (some (-38))) (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-40))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-34))) (.leaf
  (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-44))) (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-44))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))) (.node (.node (.leaf (some (-49)))
  (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none)) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-122))) (.leaf (some (-34))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-116)))
  (.leaf (some (-46))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-81))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-73))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some
  (-65))) (.leaf (some (-34))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-30))) (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-91))) (.leaf (some (-36))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf
  (some (-42))) (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-32))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-44))) (.leaf (some (-34))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node
  (.leaf (some (-42))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-36))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-40))) (.leaf (some (-42))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node
  (.leaf (some (-34))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))) (.node (.node (.leaf (some (-46))) (.leaf (some (-46))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none)) (.leaf (some (-44))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node
  (.leaf (some (-122))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-116))) (.leaf (some (-34))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-108))) (.leaf (some (-38))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.node (.leaf (some (-73))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-65))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-44))) (.leaf (some (-42))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.node (.leaf (some (-91))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-44))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-42))) (.leaf (some (-34))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.node (.leaf (some (-36))) (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-40))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-40))) (.leaf (some (-38))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.node (.leaf (some (-36))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))) (.node (.node (.leaf (some (-46))) (.leaf (some (-34))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.node (.leaf (none)) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none)) (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-116))) (.leaf (some (-36))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node
  (.leaf (some (-108))) (.leaf (some (-44))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-73))) (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-65))) (.leaf (some (-44))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.node (.leaf (some (-57))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-118))) (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-40))) (.leaf (some (-40))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.node (.leaf (some (-38))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-38))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-36))) (.leaf (some (-36))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.node (.leaf (some (-40))) (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-38))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))) (.node
  (.node (.leaf (some (-46))) (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-70))) (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none)) (.leaf (some (-38))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node
  (.leaf (some (-116))) (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-108))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-100))) (.leaf (some (-38))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.node (.leaf (some (-65))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-57))) (.leaf (some (-34))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-118))) (.leaf (some (-38))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.node (.leaf (some (-40))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-42))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-36))) (.leaf (some (-40))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.node (.leaf (some (-36))) (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-44))) (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-40))) (.leaf (some (-36))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.node (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))) (.node (.node (.leaf (some (-46))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-70))) (.leaf (some (-38))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))) (.node (.leaf (none)) (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none)) (.leaf (some (-34))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-108))) (.leaf (some (-36))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.node (.leaf (some (-100))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-65))) (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-57))) (.leaf (some (-36))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))) (.node (.leaf (some (-118))) (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-40))) (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-40))) (.leaf (some (-42)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))) (.node (.leaf (some (-40))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-40))) (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-40))) (.leaf (some
  (-42))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.node (.leaf (some (-38))) (.leaf (some (-34))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))) (.node (.node (.leaf (some (-46))) (.leaf
  (some (-44))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-70))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-62))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none)) (.leaf
  (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-108))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-100))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-92)))
  (.leaf (some (-34))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-57))) (.leaf (some (-34))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-118))) (.leaf (some (-34))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some
  (-42))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-42))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-40))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf
  (some (-38))) (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-42))) (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-42))) (.leaf (some (-40))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node
  (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))) (.node (.node (.leaf (some (-73))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-70))) (.leaf (some (-38))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.node (.leaf (some (-62))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none)) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none)) (.leaf (some (-36))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf
  (some (-100))) (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-92))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-57))) (.leaf (some (-40))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node
  (.leaf (some (-118))) (.leaf (some (-46))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-46))) (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-40))) (.leaf (some (-40))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.node (.leaf (some (-44))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-38))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-34))) (.leaf (some (-40))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.node (.leaf (some (-38))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))) (.node (.node (.leaf (some (-73))) (.leaf (some (-42))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.node (.leaf (some (-70))) (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-62))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-54))) (.leaf (some (-44))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.node (.leaf (none)) (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-100))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-92))) (.leaf (some (-38))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.node (.leaf (some (-84))) (.leaf (some (-44))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-145))) (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-38))) (.leaf (some (-38))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.node (.leaf (some (-36))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-42))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-40))) (.leaf (some (-40))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.node (.leaf (some (-44))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-34))) (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))) (.node
  (.node (.leaf (some (-73))) (.leaf (some (-34))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-95))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-62))) (.leaf (some (-40))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.node (.leaf (some (-54))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none)) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (none)) (.leaf (some (-36))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf
  (some (-92))) (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-84))) (.leaf (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-145))) (.leaf (some (-36))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node
  (.leaf (some (-46))) (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-44))) (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-34))) (.leaf (some (-38))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node
  (.leaf (some (-38))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-42))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf
  (some (-40))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)))) (.node (.node (.leaf (some (-73))) (.leaf (some (-44))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-97))) (.leaf (some (-42))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node
  (.leaf (some (-62))) (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-54))) (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-46))) (.leaf (some (-42))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node
  (.leaf (none)) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-92))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-84))) (.leaf (some (-34))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node
  (.leaf (some (-145))) (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-36))) (.leaf (some (-42))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-40))) (.leaf (some (-40))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.node (.leaf (some (-44))) (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-34))) (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-38))) (.leaf (some (-38))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.node (.leaf (some (-38))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.node (.leaf (some (-36))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))))

def tOverride : Tree16 (Tree16 (Option EdgeRes)) :=
  (.node (.node (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none))
  (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 262))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 278)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf
  ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 210)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 294))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 310))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 200)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf
  ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.dead 12))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.dead 14))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 210))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 341))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 357))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 358))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 373))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (some (.alive 389))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node
  (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 405))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (some (.alive 167))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf
  (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 159))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (some (.alive 421))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 182))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 183)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.dead 19))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 438))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 199))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 210))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (some (.dead 26))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf
  ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (some (.alive 216))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 287))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 466))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 151))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 230))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 296))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 482))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (some (.alive 210))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none))
  (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 246))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)))) (.node (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 263))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 264))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 279))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 200))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 295))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.dead 19))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 311))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 327))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 342))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (some (.alive 359))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf
  (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 151))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 374))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 174))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 390))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf
  none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 406))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 151))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 168))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 422))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 167))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 184))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf
  (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 439))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 182))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (some (.alive 200))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 451))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive
  213))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (some (.alive 217))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.dead 19))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 467))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 174))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 231))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.dead 27))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (some (.alive 246))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node
  (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive
  151))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 247))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)))) (.node (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (some (.alive 265))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)))
  (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (some (.alive 151))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 280))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 296))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (some (.alive 289))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)))
  (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 312))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.dead 28))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (some (.alive 166))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node
  (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (some (.alive 151))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 343))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 360))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 375))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 207))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 391))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 149))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (some (.alive 407))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node
  (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive
  147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 169))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 210))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 423))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (some (.alive 174))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf
  (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 185))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (some (.alive 437))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.dead 25))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 167))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 201))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 452))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 218))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 468))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (some (.alive 232))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 483))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 166))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (some (.alive 248))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)))) (.node (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 266))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 151))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 281))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf
  none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 151))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 297))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 313))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 314))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf
  none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 328))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 200))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 344))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 361))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf
  none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 210))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 376))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 392))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (some (.alive 150))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 408))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 170))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (some (.alive 424))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf
  (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 186))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 440))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 202))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 453))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 219))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 220))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (some (.alive 469))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 151))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 233))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 484))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 249))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)))) (.node (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (some (.alive 267))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node
  (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 282))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 298))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 174))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 315))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 151))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 329))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 345))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 362))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 363))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.dead 19))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 377))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 393))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 151))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 152))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 409))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 163))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (some (.dead 0))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive
  425))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 187))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 441))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (some (.alive 151))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 203))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))))
  (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (some (.alive 454))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 221))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 470)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 234))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (some (.alive 485))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (some (.alive 250))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)))) (.node (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 268)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf
  ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 151)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 283))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 299)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf
  ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (some (.alive 316))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none))
  (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 330))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 346))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 146))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 364)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf
  ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 151)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 378))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 394)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 151))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 153))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (some (.alive 410))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 171))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (some (.alive 426))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)))
  (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 188))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (some (.alive 442))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node
  (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (some (.alive 204))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (some (.alive 455))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf
  ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.dead 4))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.dead 3))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 471)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (some (.alive 235))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 486))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 314))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 251))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))))
  (.node (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (some (.alive 269))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 270))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (some (.alive 284))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)))
  (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (some (.alive 300))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 317))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 331))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 347))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.dead 13))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (some (.dead 21))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf
  (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 210))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 379))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.dead 19))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive
  395))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 154))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 151))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (some (.alive 411))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (some (.dead 1))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.dead 0))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 427))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 189))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 443))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 205))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 456))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 222))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive
  213))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 472))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 210))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 236))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 487))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 252))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)))) (.node (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 271))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 285))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (some (.alive 301))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node
  (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (some (.alive 318))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 151))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (some (.alive 332))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node
  (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (some (.alive 210))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 348))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (some (.alive 365))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node
  (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive
  147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 148))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (some (.alive 380))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf
  (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 396))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 370))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 155))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))))
  (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive
  151))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 412))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 172))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf
  ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 428)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 167))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 190))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (some (.alive 437))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none))
  (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.dead 24))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 206))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (some (.alive 151))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 457))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.dead 6))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 473))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.dead 19))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 237))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf
  (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 488))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 210))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (some (.alive 253))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)))) (.node (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.dead 7))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.dead 5))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 210))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 286))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 302))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 319))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive
  320))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none))
  (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (some (.alive 333))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf
  (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 349))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 366))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 381))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 397))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 213))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (some (.alive 156))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf
  (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 157))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 413))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 167))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 173)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 429))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 191))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 444))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 167))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (some (.alive 207))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 458))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 213))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 223))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 474))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 264))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (some (.alive 151))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none))
  (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 238))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 151))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 489))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 254))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)))) (.node (.node (.leaf
  (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 272))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 264))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 287))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 246))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf
  none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 210))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 303))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 321))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 210))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 334))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 151))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 350))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 367))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 382))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 398))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (some (.alive 158))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf
  (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 159))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (some (.alive 151))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 414))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 174))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 175)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 151))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 430))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.dead 19))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (some (.alive 192))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.dead 18))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 208))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 459))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive
  246))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 224))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 475))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (some (.alive 213))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (some (.alive 210))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 239))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))))
  (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive
  210))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 490))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 255))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)))) (.node (.node (.leaf (.leaf
  none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 273))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 151))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 288))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf
  none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 304))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.dead 10))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.dead 17)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf
  ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 335)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 213))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 351))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 368)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf
  ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 210)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 383))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 399))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.dead 23))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 151))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 160))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 415))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (some (.alive 213))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)))
  (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 176))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 431))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 193))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 445))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 209))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive
  200))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 460))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 225)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 476))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 151))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 240))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 491))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 256))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)))) (.node (.node (.leaf
  (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 274))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 210))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 289))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf
  none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 174))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 305))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.dead 19))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive
  322))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none))
  (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive
  151))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 336))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive
  352))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none))
  (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.dead 15)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.dead 20))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 384))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 400))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 161))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (some (.alive 210))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 416))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 174))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 177))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 174))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 432))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 151))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 194))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 446))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 210))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 201))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 461))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 226))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 477))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive
  241))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 492))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 257)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)))) (.node (.node
  (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 275))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 151))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (some (.alive 290))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node
  (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 306))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 323))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 210))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 337))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 353))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 369))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 385))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (some (.alive 401))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf
  ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (some (.alive 162))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 417))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 246))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 178))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive
  433))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (some (.alive 195))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 174))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 447)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 211))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (some (.alive 462))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (some (.dead 8))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.dead 2))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 478))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (some (.alive 242))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf
  (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 493))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 258))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)))) (.node (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (some (.alive 276))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node
  (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 291))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (some (.alive 307))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node
  (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 324))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (some (.alive 338))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node
  (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (some (.alive 354))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 200))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 328))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (some (.alive 370))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node
  (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 386))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 402))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 163))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 164)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 151))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 418))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 179))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (some (.alive 434))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf
  ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 196))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 151))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 448))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (some (.alive 212))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf
  (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 213))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 463))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 227)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 479))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 243))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.dead 22))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 358))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 259))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)))) (.node (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.dead 11))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.dead 9))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf
  none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 292))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 308))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf
  none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 325))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 339))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))
  (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 355))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 246))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 151))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 371))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 387))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf
  none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 403))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.dead 16))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 165))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf
  ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 210)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 419))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 180))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 435))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 436))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 197))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 449))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 214))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 151))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 464))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 228))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 151))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 480))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 210))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 244))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 260))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 200))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)))) (.node (.node (.leaf (.leaf none)) (.leaf
  ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147)))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 277))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 293))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 309))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 326))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 340))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 147))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (some (.alive 356))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (some (.alive 174))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf
  (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 372))) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 388))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none))) (.node (.leaf (.leaf none)) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 404))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 163))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 420))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 167))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 181))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (some (.alive 437))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none))
  (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 370))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 198))) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (some (.dead 19))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 450))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)))))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 215))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 166))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 174))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 465))) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 229))) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 200))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 151))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (some (.alive 481))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)))
  (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 245))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 166))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none))
  (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf
  (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none))) (.node (.leaf ((.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.node (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some (.alive 261))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf
  (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.node (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (some
  (.alive 213))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))
  (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none)) (.leaf (none))))) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf
  none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)) (.leaf (.leaf none)))))

def cert : TropicCert where
  k := 10
  D_track := 4
  cn := 1
  bn := 28
  q := 4
  A := 27
  ALPHA := 145
  V := 494
  numCegar := 29
  symInfo := fun a => tSymInfo.get 2 a
  symId := fun m d t => tSymId.get 2 ((m * 5 + d) * 5 + t)
  d1State := fun a => tD1State.get 2 a
  stD0 := fun u => tStD0.get 3 u
  stPsi := fun u f => match f with | 0 => tStPsi0.get 3 u | 1 => tStPsi1.get 3 u | _ => tStPsi2.get 3 u
  stPar := fun u => tStPar.get 3 u
  stSym := fun u => tStSym.get 3 u
  maxPsi := fun s f => match f with | 0 => tMaxPsi0.get 2 s | 1 => tMaxPsi1.get 2 s | _ => tMaxPsi2.get 2 s
  cegarForb := fun fid => tCegar.get 2 fid
  pairMode := fun s a => (tPairMode.get 2 s).get 2 a
  getOverride := fun u a => (tOverride.get 3 u).get 2 a

end SuperpermLowerBounds.Tropic.TropicN10
