/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.BelorousskiPandharipandeGraphs

/-!
# The finite graph frame for the retained L24 vectors

The 815 columns cover the retained initial, correction and final vectors in
the saved exploration. Unreduced BP terms require additional auxiliary columns.
This table asserts stability, genus and degree, not a relation.
All coefficients use raw gluing pushforwards, with external labels 0 through 3.
-/

@[expose] public section

namespace AxiomaticGW.L24Graphs
open RelationCertificate

set_option maxRecDepth 20000

/-- Original admcycles indices, retained only for traceable diagnostics. -/
def upstreamIndex : Fin 815 → ℕ :=
  (fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then
    (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1
    then 47 else (if i.val < 2 then 48 else 49)) else (if i.val < 4 then 50 else (if i.val < 5
    then 57 else 58))) else (if i.val < 9 then (if i.val < 7 then 60 else (if i.val < 8 then 68
    else 69)) else (if i.val < 10 then 71 else (if i.val < 11 then 85 else 88)))) else (if i.val
    < 18 then (if i.val < 15 then (if i.val < 13 then 90 else (if i.val < 14 then 93 else 94))
    else (if i.val < 16 then 101 else (if i.val < 17 then 102 else 103))) else (if i.val < 21
    then (if i.val < 19 then 105 else (if i.val < 20 then 112 else 113)) else (if i.val < 23
    then (if i.val < 22 then 114 else 116) else (if i.val < 24 then 129 else 130))))) else (if
    i.val < 37 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then 131 else (if
    i.val < 27 then 132 else 133)) else (if i.val < 29 then 134 else (if i.val < 30 then 137
    else 138))) else (if i.val < 34 then (if i.val < 32 then 145 else (if i.val < 33 then 146
    else 148)) else (if i.val < 35 then 163 else (if i.val < 36 then 164 else 167)))) else (if
    i.val < 43 then (if i.val < 40 then (if i.val < 38 then 170 else (if i.val < 39 then 171
    else 185)) else (if i.val < 41 then 186 else (if i.val < 42 then 189 else 192))) else (if
    i.val < 46 then (if i.val < 44 then 193 else (if i.val < 45 then 214 else 219)) else (if
    i.val < 48 then (if i.val < 47 then 223 else 226) else (if i.val < 49 then 230 else
    231)))))) else (if i.val < 75 then (if i.val < 62 then (if i.val < 56 then (if i.val < 53
    then (if i.val < 51 then 233 else (if i.val < 52 then 234 else 236)) else (if i.val < 54
    then 237 else (if i.val < 55 then 240 else 241))) else (if i.val < 59 then (if i.val < 57
    then 244 else (if i.val < 58 then 246 else 247)) else (if i.val < 60 then 249 else (if i.val
    < 61 then 250 else 252)))) else (if i.val < 68 then (if i.val < 65 then (if i.val < 63 then
    253 else (if i.val < 64 then 260 else 262)) else (if i.val < 66 then 263 else (if i.val < 67
    then 265 else 266))) else (if i.val < 71 then (if i.val < 69 then 268 else (if i.val < 70
    then 269 else 276)) else (if i.val < 73 then (if i.val < 72 then 279 else 280) else (if
    i.val < 74 then 281 else 283))))) else (if i.val < 88 then (if i.val < 81 then (if i.val <
    78 then (if i.val < 76 then 285 else (if i.val < 77 then 286 else 288)) else (if i.val < 79
    then 289 else (if i.val < 80 then 292 else 293))) else (if i.val < 84 then (if i.val < 82
    then 296 else (if i.val < 83 then 298 else 299)) else (if i.val < 86 then (if i.val < 85
    then 301 else 302) else (if i.val < 87 then 305 else 306)))) else (if i.val < 94 then (if
    i.val < 91 then (if i.val < 89 then 309 else (if i.val < 90 then 312 else 313)) else (if
    i.val < 92 then 314 else (if i.val < 93 then 316 else 318))) else (if i.val < 97 then (if
    i.val < 95 then 319 else (if i.val < 96 then 321 else 322)) else (if i.val < 99 then (if
    i.val < 98 then 329 else 332) else (if i.val < 100 then 333 else 334))))))) else (if i.val <
    152 then (if i.val < 126 then (if i.val < 113 then (if i.val < 107 then (if i.val < 104 then
    (if i.val < 102 then 336 else (if i.val < 103 then 339 else 340)) else (if i.val < 105 then
    341 else (if i.val < 106 then 343 else 344))) else (if i.val < 110 then (if i.val < 108 then
    345 else (if i.val < 109 then 346 else 347)) else (if i.val < 111 then 348 else (if i.val <
    112 then 349 else 350)))) else (if i.val < 119 then (if i.val < 116 then (if i.val < 114
    then 351 else (if i.val < 115 then 352 else 353)) else (if i.val < 117 then 354 else (if
    i.val < 118 then 355 else 356))) else (if i.val < 122 then (if i.val < 120 then 357 else (if
    i.val < 121 then 358 else 624)) else (if i.val < 124 then (if i.val < 123 then 625 else 626)
    else (if i.val < 125 then 627 else 630))))) else (if i.val < 139 then (if i.val < 132 then
    (if i.val < 129 then (if i.val < 127 then 631 else (if i.val < 128 then 632 else 633)) else
    (if i.val < 130 then 634 else (if i.val < 131 then 637 else 638))) else (if i.val < 135 then
    (if i.val < 133 then 639 else (if i.val < 134 then 640 else 641)) else (if i.val < 137 then
    (if i.val < 136 then 644 else 645) else (if i.val < 138 then 646 else 647)))) else (if i.val
    < 145 then (if i.val < 142 then (if i.val < 140 then 648 else (if i.val < 141 then 650 else
    651)) else (if i.val < 143 then 653 else (if i.val < 144 then 657 else 658))) else (if i.val
    < 148 then (if i.val < 146 then 659 else (if i.val < 147 then 660 else 663)) else (if i.val
    < 150 then (if i.val < 149 then 664 else 665) else (if i.val < 151 then 667 else 670))))))
    else (if i.val < 177 then (if i.val < 164 then (if i.val < 158 then (if i.val < 155 then (if
    i.val < 153 then 672 else (if i.val < 154 then 673 else 674)) else (if i.val < 156 then 676
    else (if i.val < 157 then 677 else 679))) else (if i.val < 161 then (if i.val < 159 then 683
    else (if i.val < 160 then 684 else 685)) else (if i.val < 162 then 686 else (if i.val < 163
    then 689 else 690)))) else (if i.val < 170 then (if i.val < 167 then (if i.val < 165 then
    691 else (if i.val < 166 then 693 else 696)) else (if i.val < 168 then 698 else (if i.val <
    169 then 699 else 700))) else (if i.val < 173 then (if i.val < 171 then 703 else (if i.val <
    172 then 704 else 705)) else (if i.val < 175 then (if i.val < 174 then 707 else 708) else
    (if i.val < 176 then 709 else 714))))) else (if i.val < 190 then (if i.val < 183 then (if
    i.val < 180 then (if i.val < 178 then 715 else (if i.val < 179 then 717 else 718)) else (if
    i.val < 181 then 719 else (if i.val < 182 then 720 else 722))) else (if i.val < 186 then (if
    i.val < 184 then 723 else (if i.val < 185 then 724 else 725)) else (if i.val < 188 then (if
    i.val < 187 then 728 else 729) else (if i.val < 189 then 730 else 731)))) else (if i.val <
    196 then (if i.val < 193 then (if i.val < 191 then 732 else (if i.val < 192 then 735 else
    736)) else (if i.val < 194 then 737 else (if i.val < 195 then 738 else 739))) else (if i.val
    < 199 then (if i.val < 197 then 742 else (if i.val < 198 then 743 else 744)) else (if i.val
    < 201 then (if i.val < 200 then 745 else 746) else (if i.val < 202 then 748 else 749))))))))
    else (if i.val < 305 then (if i.val < 254 then (if i.val < 228 then (if i.val < 215 then (if
    i.val < 209 then (if i.val < 206 then (if i.val < 204 then 750 else (if i.val < 205 then 751
    else 754)) else (if i.val < 207 then 755 else (if i.val < 208 then 756 else 757))) else (if
    i.val < 212 then (if i.val < 210 then 758 else (if i.val < 211 then 761 else 762)) else (if
    i.val < 213 then 763 else (if i.val < 214 then 764 else 765)))) else (if i.val < 221 then
    (if i.val < 218 then (if i.val < 216 then 768 else (if i.val < 217 then 769 else 770)) else
    (if i.val < 219 then 771 else (if i.val < 220 then 772 else 775))) else (if i.val < 224 then
    (if i.val < 222 then 776 else (if i.val < 223 then 777 else 779)) else (if i.val < 226 then
    (if i.val < 225 then 780 else 781) else (if i.val < 227 then 785 else 786))))) else (if
    i.val < 241 then (if i.val < 234 then (if i.val < 231 then (if i.val < 229 then 787 else (if
    i.val < 230 then 789 else 790)) else (if i.val < 232 then 791 else (if i.val < 233 then 792
    else 794))) else (if i.val < 237 then (if i.val < 235 then 795 else (if i.val < 236 then 797
    else 801)) else (if i.val < 239 then (if i.val < 238 then 802 else 803) else (if i.val < 240
    then 804 else 807)))) else (if i.val < 247 then (if i.val < 244 then (if i.val < 242 then
    808 else (if i.val < 243 then 809 else 811)) else (if i.val < 245 then 814 else (if i.val <
    246 then 816 else 817))) else (if i.val < 250 then (if i.val < 248 then 818 else (if i.val <
    249 then 821 else 822)) else (if i.val < 252 then (if i.val < 251 then 823 else 825) else
    (if i.val < 253 then 826 else 827)))))) else (if i.val < 279 then (if i.val < 266 then (if
    i.val < 260 then (if i.val < 257 then (if i.val < 255 then 831 else (if i.val < 256 then 833
    else 835)) else (if i.val < 258 then 836 else (if i.val < 259 then 837 else 838))) else (if
    i.val < 263 then (if i.val < 261 then 841 else (if i.val < 262 then 842 else 843)) else (if
    i.val < 264 then 845 else (if i.val < 265 then 846 else 847)))) else (if i.val < 272 then
    (if i.val < 269 then (if i.val < 267 then 851 else (if i.val < 268 then 853 else 855)) else
    (if i.val < 270 then 856 else (if i.val < 271 then 857 else 858))) else (if i.val < 275 then
    (if i.val < 273 then 861 else (if i.val < 274 then 862 else 863)) else (if i.val < 277 then
    (if i.val < 276 then 864 else 870) else (if i.val < 278 then 875 else 880))))) else (if
    i.val < 292 then (if i.val < 285 then (if i.val < 282 then (if i.val < 280 then 881 else (if
    i.val < 281 then 884 else 885)) else (if i.val < 283 then 888 else (if i.val < 284 then 889
    else 890))) else (if i.val < 288 then (if i.val < 286 then 895 else (if i.val < 287 then 898
    else 899)) else (if i.val < 290 then (if i.val < 289 then 904 else 907) else (if i.val < 291
    then 908 else 912)))) else (if i.val < 298 then (if i.val < 295 then (if i.val < 293 then
    913 else (if i.val < 294 then 914 else 917)) else (if i.val < 296 then 920 else (if i.val <
    297 then 926 else 927))) else (if i.val < 301 then (if i.val < 299 then 930 else (if i.val <
    300 then 931 else 935)) else (if i.val < 303 then (if i.val < 302 then 936 else 939) else
    (if i.val < 304 then 940 else 944))))))) else (if i.val < 356 then (if i.val < 330 then (if
    i.val < 317 then (if i.val < 311 then (if i.val < 308 then (if i.val < 306 then 945 else (if
    i.val < 307 then 946 else 949)) else (if i.val < 309 then 953 else (if i.val < 310 then 957
    else 958))) else (if i.val < 314 then (if i.val < 312 then 962 else (if i.val < 313 then 963
    else 964)) else (if i.val < 315 then 967 else (if i.val < 316 then 971 else 972)))) else (if
    i.val < 323 then (if i.val < 320 then (if i.val < 318 then 973 else (if i.val < 319 then 976
    else 979)) else (if i.val < 321 then 980 else (if i.val < 322 then 981 else 982))) else (if
    i.val < 326 then (if i.val < 324 then 986 else (if i.val < 325 then 988 else 989)) else (if
    i.val < 328 then (if i.val < 327 then 993 else 995) else (if i.val < 329 then 996 else
    1001))))) else (if i.val < 343 then (if i.val < 336 then (if i.val < 333 then (if i.val <
    331 then 1003 else (if i.val < 332 then 1004 else 1007)) else (if i.val < 334 then 1011 else
    (if i.val < 335 then 1013 else 1014))) else (if i.val < 339 then (if i.val < 337 then 1019
    else (if i.val < 338 then 1021 else 1022)) else (if i.val < 341 then (if i.val < 340 then
    1025 else 1030) else (if i.val < 342 then 1032 else 1033)))) else (if i.val < 349 then (if
    i.val < 346 then (if i.val < 344 then 1036 else (if i.val < 345 then 1040 else 1042)) else
    (if i.val < 347 then 1043 else (if i.val < 348 then 1047 else 1049))) else (if i.val < 352
    then (if i.val < 350 then 1050 else (if i.val < 351 then 1055 else 1057)) else (if i.val <
    354 then (if i.val < 353 then 1058 else 1061) else (if i.val < 355 then 1065 else 1067))))))
    else (if i.val < 381 then (if i.val < 368 then (if i.val < 362 then (if i.val < 359 then (if
    i.val < 357 then 1068 else (if i.val < 358 then 1073 else 1075)) else (if i.val < 360 then
    1076 else (if i.val < 361 then 1079 else 1083))) else (if i.val < 365 then (if i.val < 363
    then 1084 else (if i.val < 364 then 1086 else 1093)) else (if i.val < 366 then 1097 else (if
    i.val < 367 then 1104 else 1112)))) else (if i.val < 374 then (if i.val < 371 then (if i.val
    < 369 then 1114 else (if i.val < 370 then 1115 else 1118)) else (if i.val < 372 then 1122
    else (if i.val < 373 then 1123 else 1125))) else (if i.val < 377 then (if i.val < 375 then
    1129 else (if i.val < 376 then 1130 else 1132)) else (if i.val < 379 then (if i.val < 378
    then 1134 else 1135) else (if i.val < 380 then 1136 else 1137))))) else (if i.val < 394 then
    (if i.val < 387 then (if i.val < 384 then (if i.val < 382 then 1138 else (if i.val < 383
    then 1139 else 1140)) else (if i.val < 385 then 1141 else (if i.val < 386 then 1142 else
    1143))) else (if i.val < 390 then (if i.val < 388 then 1144 else (if i.val < 389 then 1145
    else 1146)) else (if i.val < 392 then (if i.val < 391 then 1147 else 1148) else (if i.val <
    393 then 1149 else 1150)))) else (if i.val < 400 then (if i.val < 397 then (if i.val < 395
    then 1151 else (if i.val < 396 then 1152 else 1153)) else (if i.val < 398 then 1154 else (if
    i.val < 399 then 1155 else 1156))) else (if i.val < 403 then (if i.val < 401 then 1157 else
    (if i.val < 402 then 1158 else 1159)) else (if i.val < 405 then (if i.val < 404 then 1160
    else 1161) else (if i.val < 406 then 1162 else 1163))))))))) else (if i.val < 611 then (if
    i.val < 509 then (if i.val < 458 then (if i.val < 432 then (if i.val < 419 then (if i.val <
    413 then (if i.val < 410 then (if i.val < 408 then 1164 else (if i.val < 409 then 1165 else
    1166)) else (if i.val < 411 then 1167 else (if i.val < 412 then 1168 else 1169))) else (if
    i.val < 416 then (if i.val < 414 then 1170 else (if i.val < 415 then 1171 else 1172)) else
    (if i.val < 417 then 1173 else (if i.val < 418 then 1174 else 1175)))) else (if i.val < 425
    then (if i.val < 422 then (if i.val < 420 then 1176 else (if i.val < 421 then 1177 else
    1178)) else (if i.val < 423 then 1179 else (if i.val < 424 then 1180 else 1181))) else (if
    i.val < 428 then (if i.val < 426 then 1182 else (if i.val < 427 then 1183 else 1184)) else
    (if i.val < 430 then (if i.val < 429 then 1185 else 1186) else (if i.val < 431 then 1187
    else 1188))))) else (if i.val < 445 then (if i.val < 438 then (if i.val < 435 then (if i.val
    < 433 then 1189 else (if i.val < 434 then 1190 else 1191)) else (if i.val < 436 then 1192
    else (if i.val < 437 then 1193 else 1194))) else (if i.val < 441 then (if i.val < 439 then
    1195 else (if i.val < 440 then 1196 else 1197)) else (if i.val < 443 then (if i.val < 442
    then 1198 else 1199) else (if i.val < 444 then 1200 else 1201)))) else (if i.val < 451 then
    (if i.val < 448 then (if i.val < 446 then 1202 else (if i.val < 447 then 1203 else 1204))
    else (if i.val < 449 then 1205 else (if i.val < 450 then 1206 else 1207))) else (if i.val <
    454 then (if i.val < 452 then 1208 else (if i.val < 453 then 1209 else 1210)) else (if i.val
    < 456 then (if i.val < 455 then 1211 else 1212) else (if i.val < 457 then 1213 else
    1214)))))) else (if i.val < 483 then (if i.val < 470 then (if i.val < 464 then (if i.val <
    461 then (if i.val < 459 then 1215 else (if i.val < 460 then 1216 else 1217)) else (if i.val
    < 462 then 1218 else (if i.val < 463 then 1219 else 1220))) else (if i.val < 467 then (if
    i.val < 465 then 1221 else (if i.val < 466 then 1222 else 1223)) else (if i.val < 468 then
    1224 else (if i.val < 469 then 1225 else 1226)))) else (if i.val < 476 then (if i.val < 473
    then (if i.val < 471 then 1227 else (if i.val < 472 then 1228 else 1229)) else (if i.val <
    474 then 1230 else (if i.val < 475 then 1231 else 1232))) else (if i.val < 479 then (if
    i.val < 477 then 1233 else (if i.val < 478 then 1234 else 1235)) else (if i.val < 481 then
    (if i.val < 480 then 1236 else 1237) else (if i.val < 482 then 1238 else 1239))))) else (if
    i.val < 496 then (if i.val < 489 then (if i.val < 486 then (if i.val < 484 then 1240 else
    (if i.val < 485 then 1241 else 1242)) else (if i.val < 487 then 1243 else (if i.val < 488
    then 1244 else 1245))) else (if i.val < 492 then (if i.val < 490 then 1343 else (if i.val <
    491 then 1345 else 1347)) else (if i.val < 494 then (if i.val < 493 then 1349 else 1351)
    else (if i.val < 495 then 1353 else 1355)))) else (if i.val < 502 then (if i.val < 499 then
    (if i.val < 497 then 1357 else (if i.val < 498 then 1359 else 1361)) else (if i.val < 500
    then 1418 else (if i.val < 501 then 1419 else 1420))) else (if i.val < 505 then (if i.val <
    503 then 1421 else (if i.val < 504 then 1423 else 1424)) else (if i.val < 507 then (if i.val
    < 506 then 1425 else 1428) else (if i.val < 508 then 1429 else 1430))))))) else (if i.val <
    560 then (if i.val < 534 then (if i.val < 521 then (if i.val < 515 then (if i.val < 512 then
    (if i.val < 510 then 1434 else (if i.val < 511 then 1435 else 1436)) else (if i.val < 513
    then 1437 else (if i.val < 514 then 1439 else 1440))) else (if i.val < 518 then (if i.val <
    516 then 1442 else (if i.val < 517 then 1443 else 1444)) else (if i.val < 519 then 1445 else
    (if i.val < 520 then 1447 else 1448)))) else (if i.val < 527 then (if i.val < 524 then (if
    i.val < 522 then 1449 else (if i.val < 523 then 1450 else 1453)) else (if i.val < 525 then
    1454 else (if i.val < 526 then 1455 else 1456))) else (if i.val < 530 then (if i.val < 528
    then 1458 else (if i.val < 529 then 1459 else 1461)) else (if i.val < 532 then (if i.val <
    531 then 1462 else 1463) else (if i.val < 533 then 1467 else 1468))))) else (if i.val < 547
    then (if i.val < 540 then (if i.val < 537 then (if i.val < 535 then 1469 else (if i.val <
    536 then 1470 else 1472)) else (if i.val < 538 then 1473 else (if i.val < 539 then 1476 else
    1477))) else (if i.val < 543 then (if i.val < 541 then 1478 else (if i.val < 542 then 1479
    else 1481)) else (if i.val < 545 then (if i.val < 544 then 1482 else 1486) else (if i.val <
    546 then 1487 else 1488)))) else (if i.val < 553 then (if i.val < 550 then (if i.val < 548
    then 1489 else (if i.val < 549 then 1495 else 1500)) else (if i.val < 551 then 1505 else (if
    i.val < 552 then 1506 else 1508))) else (if i.val < 556 then (if i.val < 554 then 1509 else
    (if i.val < 555 then 1512 else 1513)) else (if i.val < 558 then (if i.val < 557 then 1514
    else 1518) else (if i.val < 559 then 1519 else 1521)))))) else (if i.val < 585 then (if
    i.val < 572 then (if i.val < 566 then (if i.val < 563 then (if i.val < 561 then 1522 else
    (if i.val < 562 then 1526 else 1527)) else (if i.val < 564 then 1529 else (if i.val < 565
    then 1530 else 1534))) else (if i.val < 569 then (if i.val < 567 then 1535 else (if i.val <
    568 then 1536 else 1538)) else (if i.val < 570 then 1541 else (if i.val < 571 then 1547 else
    1548)))) else (if i.val < 578 then (if i.val < 575 then (if i.val < 573 then 1550 else (if
    i.val < 574 then 1551 else 1555)) else (if i.val < 576 then 1556 else (if i.val < 577 then
    1558 else 1559))) else (if i.val < 581 then (if i.val < 579 then 1563 else (if i.val < 580
    then 1564 else 1565)) else (if i.val < 583 then (if i.val < 582 then 1567 else 1571) else
    (if i.val < 584 then 1572 else 1574))))) else (if i.val < 598 then (if i.val < 591 then (if
    i.val < 588 then (if i.val < 586 then 1575 else (if i.val < 587 then 1579 else 1580)) else
    (if i.val < 589 then 1581 else (if i.val < 590 then 1583 else 1587))) else (if i.val < 594
    then (if i.val < 592 then 1588 else (if i.val < 593 then 1589 else 1591)) else (if i.val <
    596 then (if i.val < 595 then 1595 else 1596) else (if i.val < 597 then 1597 else 1598))))
    else (if i.val < 604 then (if i.val < 601 then (if i.val < 599 then 1601 else (if i.val <
    600 then 1602 else 1603)) else (if i.val < 602 then 1604 else (if i.val < 603 then 1609 else
    1611))) else (if i.val < 607 then (if i.val < 605 then 1612 else (if i.val < 606 then 1613
    else 1618)) else (if i.val < 609 then (if i.val < 608 then 1620 else 1621) else (if i.val <
    610 then 1622 else 1627)))))))) else (if i.val < 713 then (if i.val < 662 then (if i.val <
    636 then (if i.val < 623 then (if i.val < 617 then (if i.val < 614 then (if i.val < 612 then
    1628 else (if i.val < 613 then 1630 else 1631)) else (if i.val < 615 then 1636 else (if
    i.val < 616 then 1638 else 1639))) else (if i.val < 620 then (if i.val < 618 then 1640 else
    (if i.val < 619 then 1645 else 1646)) else (if i.val < 621 then 1648 else (if i.val < 622
    then 1649 else 1654)))) else (if i.val < 629 then (if i.val < 626 then (if i.val < 624 then
    1655 else (if i.val < 625 then 1657 else 1658)) else (if i.val < 627 then 1663 else (if
    i.val < 628 then 1664 else 1665))) else (if i.val < 632 then (if i.val < 630 then 1667 else
    (if i.val < 631 then 1672 else 1674)) else (if i.val < 634 then (if i.val < 633 then 1675
    else 1676) else (if i.val < 635 then 1681 else 1682))))) else (if i.val < 649 then (if i.val
    < 642 then (if i.val < 639 then (if i.val < 637 then 1684 else (if i.val < 638 then 1685
    else 1690)) else (if i.val < 640 then 1691 else (if i.val < 641 then 1693 else 1694))) else
    (if i.val < 645 then (if i.val < 643 then 1699 else (if i.val < 644 then 1700 else 1701))
    else (if i.val < 647 then (if i.val < 646 then 1703 else 1708) else (if i.val < 648 then
    1709 else 1711)))) else (if i.val < 655 then (if i.val < 652 then (if i.val < 650 then 1712
    else (if i.val < 651 then 1717 else 1718)) else (if i.val < 653 then 1719 else (if i.val <
    654 then 1721 else 1726))) else (if i.val < 658 then (if i.val < 656 then 1727 else (if
    i.val < 657 then 1728 else 1730)) else (if i.val < 660 then (if i.val < 659 then 1735 else
    1736) else (if i.val < 661 then 1737 else 1738)))))) else (if i.val < 687 then (if i.val <
    674 then (if i.val < 668 then (if i.val < 665 then (if i.val < 663 then 1741 else (if i.val
    < 664 then 1742 else 1743)) else (if i.val < 666 then 1744 else (if i.val < 667 then 1745
    else 1746))) else (if i.val < 671 then (if i.val < 669 then 1747 else (if i.val < 670 then
    1748 else 1749)) else (if i.val < 672 then 1750 else (if i.val < 673 then 1751 else 1752))))
    else (if i.val < 680 then (if i.val < 677 then (if i.val < 675 then 1753 else (if i.val <
    676 then 1754 else 1755)) else (if i.val < 678 then 1756 else (if i.val < 679 then 1757 else
    1758))) else (if i.val < 683 then (if i.val < 681 then 1759 else (if i.val < 682 then 1760
    else 1761)) else (if i.val < 685 then (if i.val < 684 then 1762 else 1763) else (if i.val <
    686 then 1764 else 1765))))) else (if i.val < 700 then (if i.val < 693 then (if i.val < 690
    then (if i.val < 688 then 1766 else (if i.val < 689 then 1767 else 1768)) else (if i.val <
    691 then 1769 else (if i.val < 692 then 1770 else 1771))) else (if i.val < 696 then (if
    i.val < 694 then 1772 else (if i.val < 695 then 1773 else 1774)) else (if i.val < 698 then
    (if i.val < 697 then 1775 else 1776) else (if i.val < 699 then 1777 else 1778)))) else (if
    i.val < 706 then (if i.val < 703 then (if i.val < 701 then 1779 else (if i.val < 702 then
    1780 else 1781)) else (if i.val < 704 then 1782 else (if i.val < 705 then 1783 else 1784)))
    else (if i.val < 709 then (if i.val < 707 then 1785 else (if i.val < 708 then 1786 else
    1787)) else (if i.val < 711 then (if i.val < 710 then 1788 else 1789) else (if i.val < 712
    then 1790 else 1791))))))) else (if i.val < 764 then (if i.val < 738 then (if i.val < 725
    then (if i.val < 719 then (if i.val < 716 then (if i.val < 714 then 1792 else (if i.val <
    715 then 1793 else 1794)) else (if i.val < 717 then 1795 else (if i.val < 718 then 1796 else
    1797))) else (if i.val < 722 then (if i.val < 720 then 1798 else (if i.val < 721 then 1799
    else 1800)) else (if i.val < 723 then 1801 else (if i.val < 724 then 1802 else 1803)))) else
    (if i.val < 731 then (if i.val < 728 then (if i.val < 726 then 1804 else (if i.val < 727
    then 1805 else 1806)) else (if i.val < 729 then 1807 else (if i.val < 730 then 1808 else
    1809))) else (if i.val < 734 then (if i.val < 732 then 1810 else (if i.val < 733 then 1811
    else 1812)) else (if i.val < 736 then (if i.val < 735 then 1813 else 1814) else (if i.val <
    737 then 1815 else 1816))))) else (if i.val < 751 then (if i.val < 744 then (if i.val < 741
    then (if i.val < 739 then 1817 else (if i.val < 740 then 1818 else 1819)) else (if i.val <
    742 then 1820 else (if i.val < 743 then 1821 else 1822))) else (if i.val < 747 then (if
    i.val < 745 then 1823 else (if i.val < 746 then 1824 else 1825)) else (if i.val < 749 then
    (if i.val < 748 then 1826 else 1827) else (if i.val < 750 then 1828 else 1829)))) else (if
    i.val < 757 then (if i.val < 754 then (if i.val < 752 then 1830 else (if i.val < 753 then
    1831 else 1832)) else (if i.val < 755 then 1833 else (if i.val < 756 then 1834 else 1835)))
    else (if i.val < 760 then (if i.val < 758 then 1836 else (if i.val < 759 then 1837 else
    1838)) else (if i.val < 762 then (if i.val < 761 then 1839 else 1840) else (if i.val < 763
    then 1841 else 1842)))))) else (if i.val < 789 then (if i.val < 776 then (if i.val < 770
    then (if i.val < 767 then (if i.val < 765 then 1843 else (if i.val < 766 then 1844 else
    1845)) else (if i.val < 768 then 1846 else (if i.val < 769 then 1847 else 1848))) else (if
    i.val < 773 then (if i.val < 771 then 1849 else (if i.val < 772 then 1850 else 1851)) else
    (if i.val < 774 then 1852 else (if i.val < 775 then 1853 else 1854)))) else (if i.val < 782
    then (if i.val < 779 then (if i.val < 777 then 1855 else (if i.val < 778 then 1856 else
    1857)) else (if i.val < 780 then 1858 else (if i.val < 781 then 1859 else 1860))) else (if
    i.val < 785 then (if i.val < 783 then 1861 else (if i.val < 784 then 1862 else 1863)) else
    (if i.val < 787 then (if i.val < 786 then 1864 else 1865) else (if i.val < 788 then 1866
    else 1867))))) else (if i.val < 802 then (if i.val < 795 then (if i.val < 792 then (if i.val
    < 790 then 1868 else (if i.val < 791 then 1869 else 1870)) else (if i.val < 793 then 1871
    else (if i.val < 794 then 1872 else 1873))) else (if i.val < 798 then (if i.val < 796 then
    1874 else (if i.val < 797 then 1875 else 1876)) else (if i.val < 800 then (if i.val < 799
    then 1877 else 1878) else (if i.val < 801 then 1879 else 1880)))) else (if i.val < 808 then
    (if i.val < 805 then (if i.val < 803 then 1881 else (if i.val < 804 then 1882 else 1883))
    else (if i.val < 806 then 2048 else (if i.val < 807 then 2049 else 2050))) else (if i.val <
    811 then (if i.val < 809 then 2051 else (if i.val < 810 then 2052 else 2053)) else (if i.val
    < 813 then (if i.val < 812 then 2054 else 2055) else (if i.val < 814 then 2056 else
    2057)))))))))))

/-- Raw stable presentation of column 0 (upstream index 47). -/
def graph0 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0]] }

/-- Raw stable presentation of column 1 (upstream index 48). -/
def graph1 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 1]] }

/-- Raw stable presentation of column 2 (upstream index 49). -/
def graph2 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 2, 0, 0],
    halfEdgePsiPower := ![![0, 0]] }

/-- Raw stable presentation of column 3 (upstream index 50). -/
def graph3 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 1]] }

/-- Raw stable presentation of column 4 (upstream index 57). -/
def graph4 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![2, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0]] }

/-- Raw stable presentation of column 5 (upstream index 58). -/
def graph5 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0]] }

/-- Raw stable presentation of column 6 (upstream index 60). -/
def graph6 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 2, 0],
    halfEdgePsiPower := ![![0, 0]] }

/-- Raw stable presentation of column 7 (upstream index 68). -/
def graph7 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 1], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![2, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0]] }

/-- Raw stable presentation of column 8 (upstream index 69). -/
def graph8 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 1], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0]] }

/-- Raw stable presentation of column 9 (upstream index 71). -/
def graph9 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 1], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 2],
    halfEdgePsiPower := ![![0, 0]] }

/-- Raw stable presentation of column 10 (upstream index 85). -/
def graph10 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0]] }

/-- Raw stable presentation of column 11 (upstream index 88). -/
def graph11 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 1]] }

/-- Raw stable presentation of column 12 (upstream index 90). -/
def graph12 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 1]] }

/-- Raw stable presentation of column 13 (upstream index 93). -/
def graph13 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![2, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0]] }

/-- Raw stable presentation of column 14 (upstream index 94). -/
def graph14 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 1]] }

/-- Raw stable presentation of column 15 (upstream index 101). -/
def graph15 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 2, 0, 0],
    halfEdgePsiPower := ![![0, 0]] }

/-- Raw stable presentation of column 16 (upstream index 102). -/
def graph16 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 1, 0],
    halfEdgePsiPower := ![![0, 0]] }

/-- Raw stable presentation of column 17 (upstream index 103). -/
def graph17 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 1]] }

/-- Raw stable presentation of column 18 (upstream index 105). -/
def graph18 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 1]] }

/-- Raw stable presentation of column 19 (upstream index 112). -/
def graph19 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 1], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 2, 0, 0],
    halfEdgePsiPower := ![![0, 0]] }

/-- Raw stable presentation of column 20 (upstream index 113). -/
def graph20 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 1], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 1],
    halfEdgePsiPower := ![![0, 0]] }

/-- Raw stable presentation of column 21 (upstream index 114). -/
def graph21 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 1], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 1]] }

/-- Raw stable presentation of column 22 (upstream index 116). -/
def graph22 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 1], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 1]] }

/-- Raw stable presentation of column 23 (upstream index 129). -/
def graph23 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0]] }

/-- Raw stable presentation of column 24 (upstream index 130). -/
def graph24 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 1]] }

/-- Raw stable presentation of column 25 (upstream index 131). -/
def graph25 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 1, 0],
    halfEdgePsiPower := ![![0, 0]] }

/-- Raw stable presentation of column 26 (upstream index 132). -/
def graph26 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 1]] }

/-- Raw stable presentation of column 27 (upstream index 133). -/
def graph27 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 1],
    halfEdgePsiPower := ![![0, 0]] }

/-- Raw stable presentation of column 28 (upstream index 134). -/
def graph28 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 1]] }

/-- Raw stable presentation of column 29 (upstream index 137). -/
def graph29 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 2, 0, 0],
    halfEdgePsiPower := ![![0, 0]] }

/-- Raw stable presentation of column 30 (upstream index 138). -/
def graph30 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 1]] }

/-- Raw stable presentation of column 31 (upstream index 145). -/
def graph31 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 1], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 2, 0],
    halfEdgePsiPower := ![![0, 0]] }

/-- Raw stable presentation of column 32 (upstream index 146). -/
def graph32 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 1], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 1],
    halfEdgePsiPower := ![![0, 0]] }

/-- Raw stable presentation of column 33 (upstream index 148). -/
def graph33 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 1], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 2],
    halfEdgePsiPower := ![![0, 0]] }

/-- Raw stable presentation of column 34 (upstream index 163). -/
def graph34 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 1]] }

/-- Raw stable presentation of column 35 (upstream index 164). -/
def graph35 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 1, 0],
    halfEdgePsiPower := ![![0, 0]] }

/-- Raw stable presentation of column 36 (upstream index 167). -/
def graph36 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 1]] }

/-- Raw stable presentation of column 37 (upstream index 170). -/
def graph37 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 2, 0],
    halfEdgePsiPower := ![![0, 0]] }

/-- Raw stable presentation of column 38 (upstream index 171). -/
def graph38 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 1]] }

/-- Raw stable presentation of column 39 (upstream index 185). -/
def graph39 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 1]] }

/-- Raw stable presentation of column 40 (upstream index 186). -/
def graph40 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 1],
    halfEdgePsiPower := ![![0, 0]] }

/-- Raw stable presentation of column 41 (upstream index 189). -/
def graph41 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 1]] }

/-- Raw stable presentation of column 42 (upstream index 192). -/
def graph42 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 2],
    halfEdgePsiPower := ![![0, 0]] }

/-- Raw stable presentation of column 43 (upstream index 193). -/
def graph43 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 1]] }

/-- Raw stable presentation of column 44 (upstream index 214). -/
def graph44 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 1]] }

/-- Raw stable presentation of column 45 (upstream index 219). -/
def graph45 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 1]] }

/-- Raw stable presentation of column 46 (upstream index 223). -/
def graph46 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 1]] }

/-- Raw stable presentation of column 47 (upstream index 226). -/
def graph47 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 0], endpoint := ![![0, 1]], genus := ![0, 2] } :
        StableGraphCode.Candidate (Fin 4) 2 1).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 1]] }

/-- Raw stable presentation of column 48 (upstream index 230). -/
def graph48 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 49 (upstream index 231). -/
def graph49 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 50 (upstream index 233). -/
def graph50 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 51 (upstream index 234). -/
def graph51 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 52 (upstream index 236). -/
def graph52 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 1], ![0, 0]] }

/-- Raw stable presentation of column 53 (upstream index 237). -/
def graph53 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 54 (upstream index 240). -/
def graph54 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 55 (upstream index 241). -/
def graph55 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 56 (upstream index 244). -/
def graph56 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 57 (upstream index 246). -/
def graph57 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 58 (upstream index 247). -/
def graph58 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 59 (upstream index 249). -/
def graph59 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 2, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 60 (upstream index 250). -/
def graph60 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 2, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 61 (upstream index 252). -/
def graph61 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 1], ![0, 0]] }

/-- Raw stable presentation of column 62 (upstream index 253). -/
def graph62 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 63 (upstream index 260). -/
def graph63 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 64 (upstream index 262). -/
def graph64 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 65 (upstream index 263). -/
def graph65 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 66 (upstream index 265). -/
def graph66 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 67 (upstream index 266). -/
def graph67 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 68 (upstream index 268). -/
def graph68 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 1], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 1], ![0, 0]] }

/-- Raw stable presentation of column 69 (upstream index 269). -/
def graph69 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 1], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 70 (upstream index 276). -/
def graph70 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 71 (upstream index 279). -/
def graph71 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 72 (upstream index 280). -/
def graph72 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 73 (upstream index 281). -/
def graph73 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 74 (upstream index 283). -/
def graph74 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 75 (upstream index 285). -/
def graph75 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 76 (upstream index 286). -/
def graph76 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 77 (upstream index 288). -/
def graph77 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 2, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 78 (upstream index 289). -/
def graph78 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 2, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 79 (upstream index 292). -/
def graph79 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 80 (upstream index 293). -/
def graph80 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 81 (upstream index 296). -/
def graph81 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 82 (upstream index 298). -/
def graph82 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 83 (upstream index 299). -/
def graph83 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 84 (upstream index 301). -/
def graph84 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 85 (upstream index 302). -/
def graph85 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 86 (upstream index 305). -/
def graph86 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 87 (upstream index 306). -/
def graph87 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 88 (upstream index 309). -/
def graph88 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 89 (upstream index 312). -/
def graph89 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 90 (upstream index 313). -/
def graph90 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 91 (upstream index 314). -/
def graph91 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 92 (upstream index 316). -/
def graph92 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 93 (upstream index 318). -/
def graph93 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 94 (upstream index 319). -/
def graph94 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 95 (upstream index 321). -/
def graph95 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 96 (upstream index 322). -/
def graph96 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 97 (upstream index 329). -/
def graph97 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 98 (upstream index 332). -/
def graph98 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 99 (upstream index 333). -/
def graph99 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 100 (upstream index 334). -/
def graph100 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 101 (upstream index 336). -/
def graph101 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 102 (upstream index 339). -/
def graph102 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 103 (upstream index 340). -/
def graph103 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 104 (upstream index 341). -/
def graph104 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 105 (upstream index 343). -/
def graph105 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 0, 2] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 106 (upstream index 344). -/
def graph106 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 0, 0], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 0, 0,
        2] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 107 (upstream index 345). -/
def graph107 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 0, 0], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 0, 0,
        2] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 108 (upstream index 346). -/
def graph108 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 0], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 0, 0,
        2] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 109 (upstream index 347). -/
def graph109 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 1, 0], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 0, 0,
        2] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 110 (upstream index 348). -/
def graph110 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 2, 0], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 0, 0,
        2] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 111 (upstream index 349). -/
def graph111 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 0], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 0, 0,
        2] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 112 (upstream index 350). -/
def graph112 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 1], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 0, 0,
        2] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 113 (upstream index 351). -/
def graph113 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 2], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 0, 0,
        2] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 114 (upstream index 352). -/
def graph114 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 1], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 0, 0,
        2] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 115 (upstream index 353). -/
def graph115 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 1, 0], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 0, 0,
        2] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 116 (upstream index 354). -/
def graph116 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 2, 0], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 0, 0,
        2] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 117 (upstream index 355). -/
def graph117 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 1], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 0, 0,
        2] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 118 (upstream index 356). -/
def graph118 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 2], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 0, 0,
        2] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 119 (upstream index 357). -/
def graph119 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 1], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 0, 0,
        2] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 120 (upstream index 358). -/
def graph120 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 2], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 0, 0,
        2] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 121 (upstream index 624). -/
def graph121 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 2, 0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 122 (upstream index 625). -/
def graph122 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 2, 0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 123 (upstream index 626). -/
def graph123 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 2, 0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 1], ![0, 0]] }

/-- Raw stable presentation of column 124 (upstream index 627). -/
def graph124 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 2, 0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 125 (upstream index 630). -/
def graph125 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 2, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 1], ![0, 0]] }

/-- Raw stable presentation of column 126 (upstream index 631). -/
def graph126 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 2, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![1, 0]] }

/-- Raw stable presentation of column 127 (upstream index 632). -/
def graph127 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 2, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 128 (upstream index 633). -/
def graph128 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 2, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 129 (upstream index 634). -/
def graph129 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 2, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 130 (upstream index 637). -/
def graph130 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 131 (upstream index 638). -/
def graph131 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![1, 0]] }

/-- Raw stable presentation of column 132 (upstream index 639). -/
def graph132 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 133 (upstream index 640). -/
def graph133 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 1], ![0, 0]] }

/-- Raw stable presentation of column 134 (upstream index 641). -/
def graph134 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 135 (upstream index 644). -/
def graph135 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 136 (upstream index 645). -/
def graph136 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 1], ![0, 0]] }

/-- Raw stable presentation of column 137 (upstream index 646). -/
def graph137 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![1, 0]] }

/-- Raw stable presentation of column 138 (upstream index 647). -/
def graph138 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 139 (upstream index 648). -/
def graph139 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 140 (upstream index 650). -/
def graph140 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 2, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 141 (upstream index 651). -/
def graph141 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 2, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 142 (upstream index 653). -/
def graph142 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 2, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 143 (upstream index 657). -/
def graph143 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 2, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![1, 0]] }

/-- Raw stable presentation of column 144 (upstream index 658). -/
def graph144 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 2, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 145 (upstream index 659). -/
def graph145 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 2, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 146 (upstream index 660). -/
def graph146 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 2, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 147 (upstream index 663). -/
def graph147 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 1, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 148 (upstream index 664). -/
def graph148 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 1, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![1, 0]] }

/-- Raw stable presentation of column 149 (upstream index 665). -/
def graph149 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 1, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 150 (upstream index 667). -/
def graph150 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 1, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 151 (upstream index 670). -/
def graph151 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 152 (upstream index 672). -/
def graph152 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![1, 0]] }

/-- Raw stable presentation of column 153 (upstream index 673). -/
def graph153 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 154 (upstream index 674). -/
def graph154 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 155 (upstream index 676). -/
def graph155 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 2], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 156 (upstream index 677). -/
def graph156 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 2], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 157 (upstream index 679). -/
def graph157 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 2], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 158 (upstream index 683). -/
def graph158 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![1, 0]] }

/-- Raw stable presentation of column 159 (upstream index 684). -/
def graph159 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 160 (upstream index 685). -/
def graph160 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 161 (upstream index 686). -/
def graph161 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 162 (upstream index 689). -/
def graph162 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 1], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 163 (upstream index 690). -/
def graph163 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 1], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![1, 0]] }

/-- Raw stable presentation of column 164 (upstream index 691). -/
def graph164 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 1], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 165 (upstream index 693). -/
def graph165 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 1], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 166 (upstream index 696). -/
def graph166 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 167 (upstream index 698). -/
def graph167 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![1, 0]] }

/-- Raw stable presentation of column 168 (upstream index 699). -/
def graph168 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 169 (upstream index 700). -/
def graph169 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 170 (upstream index 703). -/
def graph170 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 171 (upstream index 704). -/
def graph171 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 172 (upstream index 705). -/
def graph172 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 173 (upstream index 707). -/
def graph173 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 174 (upstream index 708). -/
def graph174 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 1], ![0, 0]] }

/-- Raw stable presentation of column 175 (upstream index 709). -/
def graph175 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 176 (upstream index 714). -/
def graph176 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 177 (upstream index 715). -/
def graph177 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 178 (upstream index 717). -/
def graph178 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 1], ![0, 0]] }

/-- Raw stable presentation of column 179 (upstream index 718). -/
def graph179 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![1, 0]] }

/-- Raw stable presentation of column 180 (upstream index 719). -/
def graph180 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 181 (upstream index 720). -/
def graph181 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 182 (upstream index 722). -/
def graph182 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 2, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 183 (upstream index 723). -/
def graph183 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 2, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 184 (upstream index 724). -/
def graph184 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 2, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 1], ![0, 0]] }

/-- Raw stable presentation of column 185 (upstream index 725). -/
def graph185 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 2, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 186 (upstream index 728). -/
def graph186 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 2, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 1], ![0, 0]] }

/-- Raw stable presentation of column 187 (upstream index 729). -/
def graph187 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 2, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![1, 0]] }

/-- Raw stable presentation of column 188 (upstream index 730). -/
def graph188 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 2, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 189 (upstream index 731). -/
def graph189 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 2, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 190 (upstream index 732). -/
def graph190 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 2, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 191 (upstream index 735). -/
def graph191 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 1, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 192 (upstream index 736). -/
def graph192 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 1, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![1, 0]] }

/-- Raw stable presentation of column 193 (upstream index 737). -/
def graph193 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 1, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 194 (upstream index 738). -/
def graph194 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 1, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 1], ![0, 0]] }

/-- Raw stable presentation of column 195 (upstream index 739). -/
def graph195 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 1, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 196 (upstream index 742). -/
def graph196 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 197 (upstream index 743). -/
def graph197 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 1], ![0, 0]] }

/-- Raw stable presentation of column 198 (upstream index 744). -/
def graph198 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![1, 0]] }

/-- Raw stable presentation of column 199 (upstream index 745). -/
def graph199 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 200 (upstream index 746). -/
def graph200 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 201 (upstream index 748). -/
def graph201 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 2], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 202 (upstream index 749). -/
def graph202 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 2], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 203 (upstream index 750). -/
def graph203 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 2], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 1], ![0, 0]] }

/-- Raw stable presentation of column 204 (upstream index 751). -/
def graph204 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 2], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 205 (upstream index 754). -/
def graph205 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 1], ![0, 0]] }

/-- Raw stable presentation of column 206 (upstream index 755). -/
def graph206 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![1, 0]] }

/-- Raw stable presentation of column 207 (upstream index 756). -/
def graph207 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 208 (upstream index 757). -/
def graph208 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 209 (upstream index 758). -/
def graph209 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 210 (upstream index 761). -/
def graph210 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 1], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 211 (upstream index 762). -/
def graph211 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 1], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![1, 0]] }

/-- Raw stable presentation of column 212 (upstream index 763). -/
def graph212 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 1], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 213 (upstream index 764). -/
def graph213 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 1], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 1], ![0, 0]] }

/-- Raw stable presentation of column 214 (upstream index 765). -/
def graph214 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 1], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 215 (upstream index 768). -/
def graph215 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 216 (upstream index 769). -/
def graph216 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 1], ![0, 0]] }

/-- Raw stable presentation of column 217 (upstream index 770). -/
def graph217 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![1, 0]] }

/-- Raw stable presentation of column 218 (upstream index 771). -/
def graph218 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 219 (upstream index 772). -/
def graph219 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 220 (upstream index 775). -/
def graph220 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 221 (upstream index 776). -/
def graph221 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 222 (upstream index 777). -/
def graph222 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 223 (upstream index 779). -/
def graph223 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 224 (upstream index 780). -/
def graph224 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 1], ![0, 0]] }

/-- Raw stable presentation of column 225 (upstream index 781). -/
def graph225 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 226 (upstream index 785). -/
def graph226 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 227 (upstream index 786). -/
def graph227 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 228 (upstream index 787). -/
def graph228 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 229 (upstream index 789). -/
def graph229 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 1], ![0, 0]] }

/-- Raw stable presentation of column 230 (upstream index 790). -/
def graph230 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![1, 0]] }

/-- Raw stable presentation of column 231 (upstream index 791). -/
def graph231 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 232 (upstream index 792). -/
def graph232 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 233 (upstream index 794). -/
def graph233 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 2], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 234 (upstream index 795). -/
def graph234 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 2], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 235 (upstream index 797). -/
def graph235 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 2], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 236 (upstream index 801). -/
def graph236 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![1, 0]] }

/-- Raw stable presentation of column 237 (upstream index 802). -/
def graph237 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 238 (upstream index 803). -/
def graph238 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 239 (upstream index 804). -/
def graph239 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 240 (upstream index 807). -/
def graph240 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 1], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 241 (upstream index 808). -/
def graph241 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 1], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![1, 0]] }

/-- Raw stable presentation of column 242 (upstream index 809). -/
def graph242 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 1], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 243 (upstream index 811). -/
def graph243 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 1], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 244 (upstream index 814). -/
def graph244 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 245 (upstream index 816). -/
def graph245 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![1, 0]] }

/-- Raw stable presentation of column 246 (upstream index 817). -/
def graph246 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 247 (upstream index 818). -/
def graph247 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 248 (upstream index 821). -/
def graph248 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 249 (upstream index 822). -/
def graph249 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 250 (upstream index 823). -/
def graph250 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 251 (upstream index 825). -/
def graph251 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 252 (upstream index 826). -/
def graph252 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 1], ![0, 0]] }

/-- Raw stable presentation of column 253 (upstream index 827). -/
def graph253 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 254 (upstream index 831). -/
def graph254 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 255 (upstream index 833). -/
def graph255 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 256 (upstream index 835). -/
def graph256 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 1], ![0, 0]] }

/-- Raw stable presentation of column 257 (upstream index 836). -/
def graph257 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![1, 0]] }

/-- Raw stable presentation of column 258 (upstream index 837). -/
def graph258 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 259 (upstream index 838). -/
def graph259 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 260 (upstream index 841). -/
def graph260 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 2], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 261 (upstream index 842). -/
def graph261 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 2], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 262 (upstream index 843). -/
def graph262 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 2], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 263 (upstream index 845). -/
def graph263 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 2], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 264 (upstream index 846). -/
def graph264 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 2], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 1], ![0, 0]] }

/-- Raw stable presentation of column 265 (upstream index 847). -/
def graph265 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 2], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 266 (upstream index 851). -/
def graph266 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 267 (upstream index 853). -/
def graph267 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 268 (upstream index 855). -/
def graph268 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 1], ![0, 0]] }

/-- Raw stable presentation of column 269 (upstream index 856). -/
def graph269 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![1, 0]] }

/-- Raw stable presentation of column 270 (upstream index 857). -/
def graph270 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 271 (upstream index 858). -/
def graph271 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 272 (upstream index 861). -/
def graph272 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 273 (upstream index 862). -/
def graph273 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 274 (upstream index 863). -/
def graph274 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 275 (upstream index 864). -/
def graph275 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 276 (upstream index 870). -/
def graph276 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 2, 2, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 277 (upstream index 875). -/
def graph277 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 2, 1, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 278 (upstream index 880). -/
def graph278 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 2, 1, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 279 (upstream index 881). -/
def graph279 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 2, 1, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 280 (upstream index 884). -/
def graph280 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 2, 1, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 281 (upstream index 885). -/
def graph281 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 2, 1, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 282 (upstream index 888). -/
def graph282 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 2, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 283 (upstream index 889). -/
def graph283 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 2, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 284 (upstream index 890). -/
def graph284 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 2, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 285 (upstream index 895). -/
def graph285 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 2, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 286 (upstream index 898). -/
def graph286 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 2, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 287 (upstream index 899). -/
def graph287 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 2, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 288 (upstream index 904). -/
def graph288 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 1, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 289 (upstream index 907). -/
def graph289 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 1, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 290 (upstream index 908). -/
def graph290 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 1, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 291 (upstream index 912). -/
def graph291 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 1, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 292 (upstream index 913). -/
def graph292 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 1, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 293 (upstream index 914). -/
def graph293 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 1, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 294 (upstream index 917). -/
def graph294 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 1, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 295 (upstream index 920). -/
def graph295 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 2, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 296 (upstream index 926). -/
def graph296 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 2, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 297 (upstream index 927). -/
def graph297 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 2, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 298 (upstream index 930). -/
def graph298 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 2, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 299 (upstream index 931). -/
def graph299 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 2, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 300 (upstream index 935). -/
def graph300 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 1, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 301 (upstream index 936). -/
def graph301 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 1, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 302 (upstream index 939). -/
def graph302 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 1, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 303 (upstream index 940). -/
def graph303 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 1, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 304 (upstream index 944). -/
def graph304 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 1, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 305 (upstream index 945). -/
def graph305 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 1, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 306 (upstream index 946). -/
def graph306 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 1, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 307 (upstream index 949). -/
def graph307 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 1, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 308 (upstream index 953). -/
def graph308 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 2, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 309 (upstream index 957). -/
def graph309 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 2, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 310 (upstream index 958). -/
def graph310 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 2, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 311 (upstream index 962). -/
def graph311 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 2, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 312 (upstream index 963). -/
def graph312 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 2, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 313 (upstream index 964). -/
def graph313 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 2, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 314 (upstream index 967). -/
def graph314 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 2, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 315 (upstream index 971). -/
def graph315 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 1, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 316 (upstream index 972). -/
def graph316 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 1, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 317 (upstream index 973). -/
def graph317 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 1, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 318 (upstream index 976). -/
def graph318 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 1, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 319 (upstream index 979). -/
def graph319 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 1, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 320 (upstream index 980). -/
def graph320 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 1, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 321 (upstream index 981). -/
def graph321 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 1, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 322 (upstream index 982). -/
def graph322 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 1, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 323 (upstream index 986). -/
def graph323 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 2, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 324 (upstream index 988). -/
def graph324 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 2, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 325 (upstream index 989). -/
def graph325 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 2, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 326 (upstream index 993). -/
def graph326 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 2, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 327 (upstream index 995). -/
def graph327 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 2, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 328 (upstream index 996). -/
def graph328 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 2, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 329 (upstream index 1001). -/
def graph329 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 330 (upstream index 1003). -/
def graph330 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 331 (upstream index 1004). -/
def graph331 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 332 (upstream index 1007). -/
def graph332 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 333 (upstream index 1011). -/
def graph333 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 2, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 334 (upstream index 1013). -/
def graph334 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 2, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 335 (upstream index 1014). -/
def graph335 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 2, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 336 (upstream index 1019). -/
def graph336 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 337 (upstream index 1021). -/
def graph337 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 338 (upstream index 1022). -/
def graph338 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 339 (upstream index 1025). -/
def graph339 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 340 (upstream index 1030). -/
def graph340 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 2, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 341 (upstream index 1032). -/
def graph341 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 2, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 342 (upstream index 1033). -/
def graph342 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 2, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 343 (upstream index 1036). -/
def graph343 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 2, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 344 (upstream index 1040). -/
def graph344 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 2, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 345 (upstream index 1042). -/
def graph345 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 2, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 346 (upstream index 1043). -/
def graph346 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 2, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 347 (upstream index 1047). -/
def graph347 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 0, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 348 (upstream index 1049). -/
def graph348 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 0, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 349 (upstream index 1050). -/
def graph349 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 0, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 350 (upstream index 1055). -/
def graph350 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 351 (upstream index 1057). -/
def graph351 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 352 (upstream index 1058). -/
def graph352 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 353 (upstream index 1061). -/
def graph353 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 354 (upstream index 1065). -/
def graph354 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 0, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 355 (upstream index 1067). -/
def graph355 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 0, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 356 (upstream index 1068). -/
def graph356 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 0, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 357 (upstream index 1073). -/
def graph357 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 358 (upstream index 1075). -/
def graph358 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 359 (upstream index 1076). -/
def graph359 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 360 (upstream index 1079). -/
def graph360 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 361 (upstream index 1083). -/
def graph361 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 362 (upstream index 1084). -/
def graph362 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 363 (upstream index 1086). -/
def graph363 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 364 (upstream index 1093). -/
def graph364 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 0, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 365 (upstream index 1097). -/
def graph365 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 2, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 366 (upstream index 1104). -/
def graph366 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 1, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 367 (upstream index 1112). -/
def graph367 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 1, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 368 (upstream index 1114). -/
def graph368 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 1, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 369 (upstream index 1115). -/
def graph369 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 1, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 370 (upstream index 1118). -/
def graph370 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 1, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 371 (upstream index 1122). -/
def graph371 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 372 (upstream index 1123). -/
def graph372 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 373 (upstream index 1125). -/
def graph373 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 1, 0], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 374 (upstream index 1129). -/
def graph374 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 375 (upstream index 1130). -/
def graph375 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 376 (upstream index 1132). -/
def graph376 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 1], endpoint := ![![0, 1], ![1, 2]], genus := ![1, 0, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 377 (upstream index 1134). -/
def graph377 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![3, 1, 0, 0], endpoint := ![![0, 1], ![1, 3], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 378 (upstream index 1135). -/
def graph378 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![3, 1, 0, 0], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 379 (upstream index 1136). -/
def graph379 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 3, 0, 0], endpoint := ![![0, 1], ![1, 3], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 380 (upstream index 1137). -/
def graph380 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 3, 0, 0], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 381 (upstream index 1138). -/
def graph381 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 0], endpoint := ![![0, 3], ![1, 3], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 382 (upstream index 1139). -/
def graph382 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 0], endpoint := ![![0, 3], ![1, 2], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 383 (upstream index 1140). -/
def graph383 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 0], endpoint := ![![0, 1], ![1, 3], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 384 (upstream index 1141). -/
def graph384 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![3, 0, 1, 0], endpoint := ![![0, 1], ![1, 3], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 385 (upstream index 1142). -/
def graph385 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![3, 0, 1, 0], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 386 (upstream index 1143). -/
def graph386 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 3, 0], endpoint := ![![0, 1], ![1, 3], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 387 (upstream index 1144). -/
def graph387 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 3, 0], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 388 (upstream index 1145). -/
def graph388 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 0], endpoint := ![![0, 3], ![1, 3], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 389 (upstream index 1146). -/
def graph389 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 0], endpoint := ![![0, 3], ![1, 2], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 390 (upstream index 1147). -/
def graph390 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 0], endpoint := ![![0, 1], ![1, 3], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 391 (upstream index 1148). -/
def graph391 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![3, 0, 0, 1], endpoint := ![![0, 1], ![1, 3], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 392 (upstream index 1149). -/
def graph392 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![3, 0, 0, 1], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 393 (upstream index 1150). -/
def graph393 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 3], endpoint := ![![0, 1], ![1, 3], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 394 (upstream index 1151). -/
def graph394 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 3], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 395 (upstream index 1152). -/
def graph395 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 1], endpoint := ![![0, 3], ![1, 3], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 396 (upstream index 1153). -/
def graph396 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 1], endpoint := ![![0, 3], ![1, 2], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 397 (upstream index 1154). -/
def graph397 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 1], endpoint := ![![0, 1], ![1, 3], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 398 (upstream index 1155). -/
def graph398 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![0, 1], ![1, 3], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 399 (upstream index 1156). -/
def graph399 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 3, 1, 0], endpoint := ![![0, 1], ![1, 3], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 400 (upstream index 1157). -/
def graph400 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 3, 1, 0], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 401 (upstream index 1158). -/
def graph401 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 3, 0], endpoint := ![![0, 1], ![1, 3], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 402 (upstream index 1159). -/
def graph402 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 3, 0], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 403 (upstream index 1160). -/
def graph403 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 0], endpoint := ![![0, 1], ![1, 3], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 404 (upstream index 1161). -/
def graph404 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 3, 0, 1], endpoint := ![![0, 1], ![1, 3], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 405 (upstream index 1162). -/
def graph405 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 3, 0, 1], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 406 (upstream index 1163). -/
def graph406 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 3], endpoint := ![![0, 1], ![1, 3], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 407 (upstream index 1164). -/
def graph407 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 3], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 408 (upstream index 1165). -/
def graph408 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 1], endpoint := ![![0, 1], ![1, 3], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 409 (upstream index 1166). -/
def graph409 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![0, 1], ![1, 3], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 410 (upstream index 1167). -/
def graph410 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 3, 1], endpoint := ![![0, 1], ![1, 3], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 411 (upstream index 1168). -/
def graph411 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 3, 1], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 412 (upstream index 1169). -/
def graph412 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 3], endpoint := ![![0, 1], ![1, 3], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 413 (upstream index 1170). -/
def graph413 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 3], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 414 (upstream index 1171). -/
def graph414 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 1], endpoint := ![![0, 1], ![1, 3], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 415 (upstream index 1172). -/
def graph415 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![0, 1], ![1, 3], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 416 (upstream index 1173). -/
def graph416 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![0, 1], ![1, 3], ![2, 3]], genus := ![0, 0, 1,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 417 (upstream index 1174). -/
def graph417 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![3, 3, 0, 0], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 418 (upstream index 1175). -/
def graph418 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![3, 2, 0, 0], endpoint := ![![0, 3], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 419 (upstream index 1176). -/
def graph419 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![3, 2, 0, 0], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 420 (upstream index 1177). -/
def graph420 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 3, 0, 0], endpoint := ![![0, 3], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 421 (upstream index 1178). -/
def graph421 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 3, 0, 0], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 422 (upstream index 1179). -/
def graph422 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 2, 0, 0], endpoint := ![![0, 3], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 423 (upstream index 1180). -/
def graph423 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 2, 0, 0], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 424 (upstream index 1181). -/
def graph424 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![3, 2, 0, 0], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 425 (upstream index 1182). -/
def graph425 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 3, 0, 0], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 426 (upstream index 1183). -/
def graph426 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![3, 1, 0, 0], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 427 (upstream index 1184). -/
def graph427 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![3, 0, 3, 0], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 428 (upstream index 1185). -/
def graph428 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![3, 0, 2, 0], endpoint := ![![0, 3], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 429 (upstream index 1186). -/
def graph429 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![3, 0, 2, 0], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 430 (upstream index 1187). -/
def graph430 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 3, 0], endpoint := ![![0, 3], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 431 (upstream index 1188). -/
def graph431 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 3, 0], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 432 (upstream index 1189). -/
def graph432 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 2, 0], endpoint := ![![0, 3], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 433 (upstream index 1190). -/
def graph433 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 2, 0], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 434 (upstream index 1191). -/
def graph434 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![3, 0, 2, 0], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 435 (upstream index 1192). -/
def graph435 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 3, 0], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 436 (upstream index 1193). -/
def graph436 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![3, 0, 1, 0], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 437 (upstream index 1194). -/
def graph437 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![3, 0, 0, 3], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 438 (upstream index 1195). -/
def graph438 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![3, 0, 0, 2], endpoint := ![![0, 3], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 439 (upstream index 1196). -/
def graph439 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![3, 0, 0, 2], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 440 (upstream index 1197). -/
def graph440 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 3], endpoint := ![![0, 3], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 441 (upstream index 1198). -/
def graph441 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 3], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 442 (upstream index 1199). -/
def graph442 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 2], endpoint := ![![0, 3], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 443 (upstream index 1200). -/
def graph443 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 2], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 444 (upstream index 1201). -/
def graph444 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![3, 0, 0, 2], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 445 (upstream index 1202). -/
def graph445 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 3], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 446 (upstream index 1203). -/
def graph446 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![3, 0, 0, 1], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 447 (upstream index 1204). -/
def graph447 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![3, 0, 0, 0], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 448 (upstream index 1205). -/
def graph448 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 0], endpoint := ![![0, 3], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 449 (upstream index 1206). -/
def graph449 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 0], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 450 (upstream index 1207). -/
def graph450 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 3, 3, 0], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 451 (upstream index 1208). -/
def graph451 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 3, 2, 0], endpoint := ![![0, 3], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 452 (upstream index 1209). -/
def graph452 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 3, 2, 0], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 453 (upstream index 1210). -/
def graph453 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 3, 0], endpoint := ![![0, 3], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 454 (upstream index 1211). -/
def graph454 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 3, 0], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 455 (upstream index 1212). -/
def graph455 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 2, 0], endpoint := ![![0, 3], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 456 (upstream index 1213). -/
def graph456 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 2, 0], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 457 (upstream index 1214). -/
def graph457 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 3, 2, 0], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 458 (upstream index 1215). -/
def graph458 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 3, 0], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 459 (upstream index 1216). -/
def graph459 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 3, 1, 0], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 460 (upstream index 1217). -/
def graph460 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 3, 0, 3], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 461 (upstream index 1218). -/
def graph461 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 3, 0, 2], endpoint := ![![0, 3], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 462 (upstream index 1219). -/
def graph462 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 3, 0, 2], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 463 (upstream index 1220). -/
def graph463 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 3], endpoint := ![![0, 3], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 464 (upstream index 1221). -/
def graph464 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 3], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 465 (upstream index 1222). -/
def graph465 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 2], endpoint := ![![0, 3], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 466 (upstream index 1223). -/
def graph466 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 2], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 467 (upstream index 1224). -/
def graph467 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 3, 0, 2], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 468 (upstream index 1225). -/
def graph468 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 3], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 469 (upstream index 1226). -/
def graph469 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 3, 0, 1], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 470 (upstream index 1227). -/
def graph470 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 3, 0, 0], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 471 (upstream index 1228). -/
def graph471 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 0], endpoint := ![![0, 3], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 472 (upstream index 1229). -/
def graph472 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 0], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 473 (upstream index 1230). -/
def graph473 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 3, 3], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 474 (upstream index 1231). -/
def graph474 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 3, 2], endpoint := ![![0, 3], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 475 (upstream index 1232). -/
def graph475 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 3, 2], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 476 (upstream index 1233). -/
def graph476 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 3], endpoint := ![![0, 3], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 477 (upstream index 1234). -/
def graph477 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 3], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 478 (upstream index 1235). -/
def graph478 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 2], endpoint := ![![0, 3], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 479 (upstream index 1236). -/
def graph479 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 2], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 480 (upstream index 1237). -/
def graph480 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 3, 2], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 481 (upstream index 1238). -/
def graph481 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 3], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 482 (upstream index 1239). -/
def graph482 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 3, 1], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 483 (upstream index 1240). -/
def graph483 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 3, 0], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 484 (upstream index 1241). -/
def graph484 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 0], endpoint := ![![0, 3], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 485 (upstream index 1242). -/
def graph485 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 0], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 486 (upstream index 1243). -/
def graph486 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 3], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 487 (upstream index 1244). -/
def graph487 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 2], endpoint := ![![0, 3], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 488 (upstream index 1245). -/
def graph488 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 2], endpoint := ![![0, 2], ![1, 2], ![2, 3]], genus := ![0, 1, 0,
        1] } :
        StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 489 (upstream index 1343). -/
def graph489 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 2, 0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![1, 0]] }

/-- Raw stable presentation of column 490 (upstream index 1345). -/
def graph490 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 2, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![1, 0]] }

/-- Raw stable presentation of column 491 (upstream index 1347). -/
def graph491 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 2], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![1, 0]] }

/-- Raw stable presentation of column 492 (upstream index 1349). -/
def graph492 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![1, 0]] }

/-- Raw stable presentation of column 493 (upstream index 1351). -/
def graph493 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 2, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![1, 0]] }

/-- Raw stable presentation of column 494 (upstream index 1353). -/
def graph494 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 2], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![1, 0]] }

/-- Raw stable presentation of column 495 (upstream index 1355). -/
def graph495 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![1, 0]] }

/-- Raw stable presentation of column 496 (upstream index 1357). -/
def graph496 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 2], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![1, 0]] }

/-- Raw stable presentation of column 497 (upstream index 1359). -/
def graph497 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 0], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![1, 0]] }

/-- Raw stable presentation of column 498 (upstream index 1361). -/
def graph498 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 2], endpoint := ![![0, 2], ![1, 2]], genus := ![0, 1, 1] } :
        StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![1, 0]] }

/-- Raw stable presentation of column 499 (upstream index 1418). -/
def graph499 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![1, 0], ![0, 0]] }

/-- Raw stable presentation of column 500 (upstream index 1419). -/
def graph500 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 501 (upstream index 1420). -/
def graph501 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 502 (upstream index 1421). -/
def graph502 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 503 (upstream index 1423). -/
def graph503 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![1, 0], ![0, 0]] }

/-- Raw stable presentation of column 504 (upstream index 1424). -/
def graph504 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 505 (upstream index 1425). -/
def graph505 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 506 (upstream index 1428). -/
def graph506 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 1], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![1, 0], ![0, 0]] }

/-- Raw stable presentation of column 507 (upstream index 1429). -/
def graph507 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 1], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 508 (upstream index 1430). -/
def graph508 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 1], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 509 (upstream index 1434). -/
def graph509 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![1, 0], ![0, 0]] }

/-- Raw stable presentation of column 510 (upstream index 1435). -/
def graph510 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 511 (upstream index 1436). -/
def graph511 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 512 (upstream index 1437). -/
def graph512 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 513 (upstream index 1439). -/
def graph513 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 514 (upstream index 1440). -/
def graph514 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 515 (upstream index 1442). -/
def graph515 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![1, 0], ![0, 0]] }

/-- Raw stable presentation of column 516 (upstream index 1443). -/
def graph516 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 517 (upstream index 1444). -/
def graph517 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 518 (upstream index 1445). -/
def graph518 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 519 (upstream index 1447). -/
def graph519 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 1], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![1, 0], ![0, 0]] }

/-- Raw stable presentation of column 520 (upstream index 1448). -/
def graph520 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 1], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 521 (upstream index 1449). -/
def graph521 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 1], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 522 (upstream index 1450). -/
def graph522 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 1], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 523 (upstream index 1453). -/
def graph523 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![1, 0], ![0, 0]] }

/-- Raw stable presentation of column 524 (upstream index 1454). -/
def graph524 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 525 (upstream index 1455). -/
def graph525 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 526 (upstream index 1456). -/
def graph526 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 527 (upstream index 1458). -/
def graph527 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 528 (upstream index 1459). -/
def graph528 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 529 (upstream index 1461). -/
def graph529 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 1], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![1, 0], ![0, 0]] }

/-- Raw stable presentation of column 530 (upstream index 1462). -/
def graph530 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 1], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 531 (upstream index 1463). -/
def graph531 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 1], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 532 (upstream index 1467). -/
def graph532 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![1, 0], ![0, 0]] }

/-- Raw stable presentation of column 533 (upstream index 1468). -/
def graph533 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 534 (upstream index 1469). -/
def graph534 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 535 (upstream index 1470). -/
def graph535 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 536 (upstream index 1472). -/
def graph536 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 537 (upstream index 1473). -/
def graph537 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 538 (upstream index 1476). -/
def graph538 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![1, 0], ![0, 0]] }

/-- Raw stable presentation of column 539 (upstream index 1477). -/
def graph539 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 540 (upstream index 1478). -/
def graph540 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 541 (upstream index 1479). -/
def graph541 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 542 (upstream index 1481). -/
def graph542 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 543 (upstream index 1482). -/
def graph543 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 1]] }

/-- Raw stable presentation of column 544 (upstream index 1486). -/
def graph544 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 545 (upstream index 1487). -/
def graph545 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 546 (upstream index 1488). -/
def graph546 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 547 (upstream index 1489). -/
def graph547 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 0], endpoint := ![![1, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 548 (upstream index 1495). -/
def graph548 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 1, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 549 (upstream index 1500). -/
def graph549 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 1], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 550 (upstream index 1505). -/
def graph550 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 551 (upstream index 1506). -/
def graph551 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 552 (upstream index 1508). -/
def graph552 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 553 (upstream index 1509). -/
def graph553 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 554 (upstream index 1512). -/
def graph554 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 1], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 555 (upstream index 1513). -/
def graph555 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 1], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 556 (upstream index 1514). -/
def graph556 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 1], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 557 (upstream index 1518). -/
def graph557 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 558 (upstream index 1519). -/
def graph558 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 559 (upstream index 1521). -/
def graph559 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 560 (upstream index 1522). -/
def graph560 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 561 (upstream index 1526). -/
def graph561 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 1], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 562 (upstream index 1527). -/
def graph562 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 1], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 563 (upstream index 1529). -/
def graph563 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 1], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 564 (upstream index 1530). -/
def graph564 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 1], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 565 (upstream index 1534). -/
def graph565 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 566 (upstream index 1535). -/
def graph566 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 567 (upstream index 1536). -/
def graph567 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 568 (upstream index 1538). -/
def graph568 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 569 (upstream index 1541). -/
def graph569 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 1], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 570 (upstream index 1547). -/
def graph570 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 571 (upstream index 1548). -/
def graph571 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 572 (upstream index 1550). -/
def graph572 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 573 (upstream index 1551). -/
def graph573 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 574 (upstream index 1555). -/
def graph574 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 1], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 575 (upstream index 1556). -/
def graph575 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 1], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 576 (upstream index 1558). -/
def graph576 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 1], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 577 (upstream index 1559). -/
def graph577 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 1], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 578 (upstream index 1563). -/
def graph578 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 579 (upstream index 1564). -/
def graph579 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 580 (upstream index 1565). -/
def graph580 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 581 (upstream index 1567). -/
def graph581 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 582 (upstream index 1571). -/
def graph582 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 1], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 583 (upstream index 1572). -/
def graph583 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 1], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 584 (upstream index 1574). -/
def graph584 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 1], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 585 (upstream index 1575). -/
def graph585 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 1], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 586 (upstream index 1579). -/
def graph586 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 587 (upstream index 1580). -/
def graph587 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 588 (upstream index 1581). -/
def graph588 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 589 (upstream index 1583). -/
def graph589 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 590 (upstream index 1587). -/
def graph590 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 591 (upstream index 1588). -/
def graph591 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 592 (upstream index 1589). -/
def graph592 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 593 (upstream index 1591). -/
def graph593 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 594 (upstream index 1595). -/
def graph594 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 595 (upstream index 1596). -/
def graph595 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 596 (upstream index 1597). -/
def graph596 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 597 (upstream index 1598). -/
def graph597 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 0], endpoint := ![![0, 1], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 598 (upstream index 1601). -/
def graph598 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 1, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 599 (upstream index 1602). -/
def graph599 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 1, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 600 (upstream index 1603). -/
def graph600 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 1, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 601 (upstream index 1604). -/
def graph601 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 1, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 602 (upstream index 1609). -/
def graph602 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 1, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 603 (upstream index 1611). -/
def graph603 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 1, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 604 (upstream index 1612). -/
def graph604 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 1, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 605 (upstream index 1613). -/
def graph605 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 1, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 606 (upstream index 1618). -/
def graph606 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 607 (upstream index 1620). -/
def graph607 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 608 (upstream index 1621). -/
def graph608 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 609 (upstream index 1622). -/
def graph609 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 610 (upstream index 1627). -/
def graph610 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 611 (upstream index 1628). -/
def graph611 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 612 (upstream index 1630). -/
def graph612 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 613 (upstream index 1631). -/
def graph613 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 614 (upstream index 1636). -/
def graph614 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 615 (upstream index 1638). -/
def graph615 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 616 (upstream index 1639). -/
def graph616 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 617 (upstream index 1640). -/
def graph617 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 618 (upstream index 1645). -/
def graph618 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 619 (upstream index 1646). -/
def graph619 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 620 (upstream index 1648). -/
def graph620 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 621 (upstream index 1649). -/
def graph621 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 622 (upstream index 1654). -/
def graph622 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 623 (upstream index 1655). -/
def graph623 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 624 (upstream index 1657). -/
def graph624 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 625 (upstream index 1658). -/
def graph625 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 626 (upstream index 1663). -/
def graph626 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 627 (upstream index 1664). -/
def graph627 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 628 (upstream index 1665). -/
def graph628 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 629 (upstream index 1667). -/
def graph629 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 630 (upstream index 1672). -/
def graph630 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 631 (upstream index 1674). -/
def graph631 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 632 (upstream index 1675). -/
def graph632 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 633 (upstream index 1676). -/
def graph633 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 634 (upstream index 1681). -/
def graph634 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 635 (upstream index 1682). -/
def graph635 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 636 (upstream index 1684). -/
def graph636 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 637 (upstream index 1685). -/
def graph637 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 638 (upstream index 1690). -/
def graph638 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 639 (upstream index 1691). -/
def graph639 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 640 (upstream index 1693). -/
def graph640 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 641 (upstream index 1694). -/
def graph641 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 642 (upstream index 1699). -/
def graph642 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 643 (upstream index 1700). -/
def graph643 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 644 (upstream index 1701). -/
def graph644 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 645 (upstream index 1703). -/
def graph645 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 646 (upstream index 1708). -/
def graph646 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 647 (upstream index 1709). -/
def graph647 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 648 (upstream index 1711). -/
def graph648 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 649 (upstream index 1712). -/
def graph649 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 650 (upstream index 1717). -/
def graph650 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 651 (upstream index 1718). -/
def graph651 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 652 (upstream index 1719). -/
def graph652 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 653 (upstream index 1721). -/
def graph653 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 654 (upstream index 1726). -/
def graph654 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 655 (upstream index 1727). -/
def graph655 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 656 (upstream index 1728). -/
def graph656 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 657 (upstream index 1730). -/
def graph657 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 658 (upstream index 1735). -/
def graph658 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 659 (upstream index 1736). -/
def graph659 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 1, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 660 (upstream index 1737). -/
def graph660 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 1, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 661 (upstream index 1738). -/
def graph661 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 0], endpoint := ![![0, 0], ![0, 1]], genus := ![0, 1] } :
        StableGraphCode.Candidate (Fin 4) 2 2).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 1],
    halfEdgePsiPower := ![![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 662 (upstream index 1741). -/
def graph662 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 0, 0], endpoint := ![![2, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 663 (upstream index 1742). -/
def graph663 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 0, 0], endpoint := ![![2, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 664 (upstream index 1743). -/
def graph664 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 0], endpoint := ![![2, 2], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 665 (upstream index 1744). -/
def graph665 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 0], endpoint := ![![2, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 666 (upstream index 1745). -/
def graph666 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 2, 0, 0], endpoint := ![![1, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 667 (upstream index 1746). -/
def graph667 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 0, 0], endpoint := ![![1, 2], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 668 (upstream index 1747). -/
def graph668 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 0, 0], endpoint := ![![1, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 669 (upstream index 1748). -/
def graph669 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 0, 0], endpoint := ![![1, 2], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 670 (upstream index 1749). -/
def graph670 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 0, 0], endpoint := ![![1, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 671 (upstream index 1750). -/
def graph671 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 0], endpoint := ![![1, 2], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 672 (upstream index 1751). -/
def graph672 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 0], endpoint := ![![1, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 673 (upstream index 1752). -/
def graph673 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 2, 0, 0], endpoint := ![![1, 1], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 674 (upstream index 1753). -/
def graph674 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 2, 0, 0], endpoint := ![![1, 1], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 675 (upstream index 1754). -/
def graph675 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 0, 0], endpoint := ![![1, 1], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 676 (upstream index 1755). -/
def graph676 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 1, 0, 0], endpoint := ![![1, 1], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 677 (upstream index 1756). -/
def graph677 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 0, 0], endpoint := ![![1, 1], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 678 (upstream index 1757). -/
def graph678 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 2, 0, 0], endpoint := ![![1, 1], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 679 (upstream index 1758). -/
def graph679 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 0], endpoint := ![![1, 1], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 680 (upstream index 1759). -/
def graph680 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 0], endpoint := ![![1, 1], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 681 (upstream index 1760). -/
def graph681 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 1, 0], endpoint := ![![2, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 682 (upstream index 1761). -/
def graph682 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 2, 0], endpoint := ![![2, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 683 (upstream index 1762). -/
def graph683 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 0], endpoint := ![![2, 2], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 684 (upstream index 1763). -/
def graph684 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 0], endpoint := ![![2, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 685 (upstream index 1764). -/
def graph685 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 2, 0], endpoint := ![![1, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 686 (upstream index 1765). -/
def graph686 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 1, 0], endpoint := ![![1, 2], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 687 (upstream index 1766). -/
def graph687 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 1, 0], endpoint := ![![1, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 688 (upstream index 1767). -/
def graph688 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 2, 0], endpoint := ![![1, 2], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 689 (upstream index 1768). -/
def graph689 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 2, 0], endpoint := ![![1, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 690 (upstream index 1769). -/
def graph690 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 0], endpoint := ![![1, 2], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 691 (upstream index 1770). -/
def graph691 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 0], endpoint := ![![1, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 692 (upstream index 1771). -/
def graph692 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 2, 0], endpoint := ![![1, 1], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 693 (upstream index 1772). -/
def graph693 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 2, 0], endpoint := ![![1, 1], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 694 (upstream index 1773). -/
def graph694 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 1, 0], endpoint := ![![1, 1], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 695 (upstream index 1774). -/
def graph695 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 1, 0], endpoint := ![![1, 1], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 696 (upstream index 1775). -/
def graph696 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 2, 0], endpoint := ![![1, 1], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 697 (upstream index 1776). -/
def graph697 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 2, 0], endpoint := ![![1, 1], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 698 (upstream index 1777). -/
def graph698 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 0], endpoint := ![![1, 1], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 699 (upstream index 1778). -/
def graph699 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 0], endpoint := ![![1, 1], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 700 (upstream index 1779). -/
def graph700 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 1], endpoint := ![![2, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 701 (upstream index 1780). -/
def graph701 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 2], endpoint := ![![2, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 702 (upstream index 1781). -/
def graph702 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 1], endpoint := ![![2, 2], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 703 (upstream index 1782). -/
def graph703 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 1], endpoint := ![![2, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 704 (upstream index 1783). -/
def graph704 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 2], endpoint := ![![1, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 705 (upstream index 1784). -/
def graph705 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 1], endpoint := ![![1, 2], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 706 (upstream index 1785). -/
def graph706 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 1], endpoint := ![![1, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 707 (upstream index 1786). -/
def graph707 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 2], endpoint := ![![1, 2], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 708 (upstream index 1787). -/
def graph708 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 2], endpoint := ![![1, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 709 (upstream index 1788). -/
def graph709 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 1], endpoint := ![![1, 2], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 710 (upstream index 1789). -/
def graph710 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 1], endpoint := ![![1, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 711 (upstream index 1790). -/
def graph711 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 2], endpoint := ![![1, 1], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 712 (upstream index 1791). -/
def graph712 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 2], endpoint := ![![1, 1], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 713 (upstream index 1792). -/
def graph713 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 1], endpoint := ![![1, 1], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 714 (upstream index 1793). -/
def graph714 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 1], endpoint := ![![1, 1], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 715 (upstream index 1794). -/
def graph715 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 2], endpoint := ![![1, 1], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 716 (upstream index 1795). -/
def graph716 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 2], endpoint := ![![1, 1], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 717 (upstream index 1796). -/
def graph717 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 1], endpoint := ![![1, 1], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 718 (upstream index 1797). -/
def graph718 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 1], endpoint := ![![1, 1], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 719 (upstream index 1798). -/
def graph719 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![2, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 720 (upstream index 1799). -/
def graph720 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 0], endpoint := ![![1, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 721 (upstream index 1800). -/
def graph721 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![1, 2], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 722 (upstream index 1801). -/
def graph722 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![1, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 723 (upstream index 1802). -/
def graph723 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 0], endpoint := ![![1, 1], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 724 (upstream index 1803). -/
def graph724 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![2, 0, 0, 0], endpoint := ![![1, 1], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 725 (upstream index 1804). -/
def graph725 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![1, 1], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 726 (upstream index 1805). -/
def graph726 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![1, 1], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 727 (upstream index 1806). -/
def graph727 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 1, 0], endpoint := ![![2, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 728 (upstream index 1807). -/
def graph728 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 2, 0], endpoint := ![![2, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 729 (upstream index 1808). -/
def graph729 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 0], endpoint := ![![2, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 730 (upstream index 1809). -/
def graph730 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 2, 0], endpoint := ![![1, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 731 (upstream index 1810). -/
def graph731 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 1, 0], endpoint := ![![1, 2], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 732 (upstream index 1811). -/
def graph732 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 1, 0], endpoint := ![![1, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 733 (upstream index 1812). -/
def graph733 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 2, 0], endpoint := ![![1, 2], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 734 (upstream index 1813). -/
def graph734 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 2, 0], endpoint := ![![1, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 735 (upstream index 1814). -/
def graph735 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 0], endpoint := ![![1, 2], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 736 (upstream index 1815). -/
def graph736 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 0], endpoint := ![![1, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 737 (upstream index 1816). -/
def graph737 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 2, 0], endpoint := ![![1, 1], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 738 (upstream index 1817). -/
def graph738 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 2, 0], endpoint := ![![1, 1], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 739 (upstream index 1818). -/
def graph739 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 1, 0], endpoint := ![![1, 1], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 740 (upstream index 1819). -/
def graph740 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 1, 0], endpoint := ![![1, 1], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 741 (upstream index 1820). -/
def graph741 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 2, 0], endpoint := ![![1, 1], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 742 (upstream index 1821). -/
def graph742 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 2, 0], endpoint := ![![1, 1], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 743 (upstream index 1822). -/
def graph743 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 0], endpoint := ![![1, 1], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 744 (upstream index 1823). -/
def graph744 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 0], endpoint := ![![1, 1], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 745 (upstream index 1824). -/
def graph745 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 1], endpoint := ![![2, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 746 (upstream index 1825). -/
def graph746 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 2], endpoint := ![![2, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 747 (upstream index 1826). -/
def graph747 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 1], endpoint := ![![2, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 748 (upstream index 1827). -/
def graph748 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 2], endpoint := ![![1, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 749 (upstream index 1828). -/
def graph749 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 1], endpoint := ![![1, 2], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 750 (upstream index 1829). -/
def graph750 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 1], endpoint := ![![1, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 751 (upstream index 1830). -/
def graph751 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 2], endpoint := ![![1, 2], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 752 (upstream index 1831). -/
def graph752 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 2], endpoint := ![![1, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 753 (upstream index 1832). -/
def graph753 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 1], endpoint := ![![1, 2], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 754 (upstream index 1833). -/
def graph754 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 1], endpoint := ![![1, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 755 (upstream index 1834). -/
def graph755 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 2], endpoint := ![![1, 1], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 756 (upstream index 1835). -/
def graph756 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 2], endpoint := ![![1, 1], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 757 (upstream index 1836). -/
def graph757 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 1], endpoint := ![![1, 1], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 758 (upstream index 1837). -/
def graph758 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 1], endpoint := ![![1, 1], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 759 (upstream index 1838). -/
def graph759 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 2], endpoint := ![![1, 1], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 760 (upstream index 1839). -/
def graph760 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 2], endpoint := ![![1, 1], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 761 (upstream index 1840). -/
def graph761 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 1], endpoint := ![![1, 1], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 762 (upstream index 1841). -/
def graph762 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 1], endpoint := ![![1, 1], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 763 (upstream index 1842). -/
def graph763 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![2, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 764 (upstream index 1843). -/
def graph764 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 0], endpoint := ![![1, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 765 (upstream index 1844). -/
def graph765 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![1, 2], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 766 (upstream index 1845). -/
def graph766 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![1, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 767 (upstream index 1846). -/
def graph767 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 0], endpoint := ![![1, 1], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 768 (upstream index 1847). -/
def graph768 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 2, 0, 0], endpoint := ![![1, 1], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 769 (upstream index 1848). -/
def graph769 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![1, 1], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 770 (upstream index 1849). -/
def graph770 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![1, 1], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 771 (upstream index 1850). -/
def graph771 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 1], endpoint := ![![2, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 772 (upstream index 1851). -/
def graph772 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 2], endpoint := ![![2, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 773 (upstream index 1852). -/
def graph773 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 1], endpoint := ![![2, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 774 (upstream index 1853). -/
def graph774 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 2], endpoint := ![![1, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 775 (upstream index 1854). -/
def graph775 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 1], endpoint := ![![1, 2], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 776 (upstream index 1855). -/
def graph776 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 1], endpoint := ![![1, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 777 (upstream index 1856). -/
def graph777 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 2], endpoint := ![![1, 2], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 778 (upstream index 1857). -/
def graph778 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 2], endpoint := ![![1, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 779 (upstream index 1858). -/
def graph779 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 1], endpoint := ![![1, 2], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 780 (upstream index 1859). -/
def graph780 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 1], endpoint := ![![1, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 781 (upstream index 1860). -/
def graph781 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 2], endpoint := ![![1, 1], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 782 (upstream index 1861). -/
def graph782 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 2], endpoint := ![![1, 1], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 783 (upstream index 1862). -/
def graph783 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 1], endpoint := ![![1, 1], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 784 (upstream index 1863). -/
def graph784 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 1], endpoint := ![![1, 1], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 785 (upstream index 1864). -/
def graph785 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 2], endpoint := ![![1, 1], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 786 (upstream index 1865). -/
def graph786 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 2], endpoint := ![![1, 1], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 787 (upstream index 1866). -/
def graph787 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 1], endpoint := ![![1, 1], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 788 (upstream index 1867). -/
def graph788 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 1], endpoint := ![![1, 1], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 789 (upstream index 1868). -/
def graph789 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![2, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 790 (upstream index 1869). -/
def graph790 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 0], endpoint := ![![1, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 791 (upstream index 1870). -/
def graph791 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![1, 2], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 792 (upstream index 1871). -/
def graph792 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![1, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 793 (upstream index 1872). -/
def graph793 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 0], endpoint := ![![1, 1], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 794 (upstream index 1873). -/
def graph794 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 2, 0], endpoint := ![![1, 1], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 795 (upstream index 1874). -/
def graph795 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![1, 1], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 796 (upstream index 1875). -/
def graph796 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![1, 1], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 797 (upstream index 1876). -/
def graph797 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![2, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 798 (upstream index 1877). -/
def graph798 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 2], endpoint := ![![1, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 799 (upstream index 1878). -/
def graph799 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![1, 2], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 800 (upstream index 1879). -/
def graph800 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![1, 2], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 801 (upstream index 1880). -/
def graph801 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 2], endpoint := ![![1, 1], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 802 (upstream index 1881). -/
def graph802 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 2], endpoint := ![![1, 1], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 803 (upstream index 1882). -/
def graph803 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![1, 1], ![0, 2], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 804 (upstream index 1883). -/
def graph804 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![1, 1], ![0, 1], ![1, 2]], genus := ![0, 0, 1]
        } :
        StableGraphCode.Candidate (Fin 4) 3 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 805 (upstream index 2048). -/
def graph805 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 1, 0, 0], endpoint := ![![1, 1], ![1, 1], ![0, 1]], genus := ![0, 0] }
        :
        StableGraphCode.Candidate (Fin 4) 2 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 806 (upstream index 2049). -/
def graph806 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 1, 0], endpoint := ![![1, 1], ![1, 1], ![0, 1]], genus := ![0, 0] }
        :
        StableGraphCode.Candidate (Fin 4) 2 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 807 (upstream index 2050). -/
def graph807 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 1], endpoint := ![![1, 1], ![1, 1], ![0, 1]], genus := ![0, 0] }
        :
        StableGraphCode.Candidate (Fin 4) 2 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 808 (upstream index 2051). -/
def graph808 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![1, 0, 0, 0], endpoint := ![![1, 1], ![1, 1], ![0, 1]], genus := ![0, 0] }
        :
        StableGraphCode.Candidate (Fin 4) 2 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 809 (upstream index 2052). -/
def graph809 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 1, 0], endpoint := ![![1, 1], ![1, 1], ![0, 1]], genus := ![0, 0] }
        :
        StableGraphCode.Candidate (Fin 4) 2 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 810 (upstream index 2053). -/
def graph810 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 1], endpoint := ![![1, 1], ![1, 1], ![0, 1]], genus := ![0, 0] }
        :
        StableGraphCode.Candidate (Fin 4) 2 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 811 (upstream index 2054). -/
def graph811 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 1, 0, 0], endpoint := ![![1, 1], ![1, 1], ![0, 1]], genus := ![0, 0] }
        :
        StableGraphCode.Candidate (Fin 4) 2 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 812 (upstream index 2055). -/
def graph812 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 1], endpoint := ![![1, 1], ![1, 1], ![0, 1]], genus := ![0, 0] }
        :
        StableGraphCode.Candidate (Fin 4) 2 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 813 (upstream index 2056). -/
def graph813 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 1, 0], endpoint := ![![1, 1], ![1, 1], ![0, 1]], genus := ![0, 0] }
        :
        StableGraphCode.Candidate (Fin 4) 2 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Raw stable presentation of column 814 (upstream index 2057). -/
def graph814 : DecoratedStableGraph (Fin 4) :=
  { graph :=
      ({ legVertex := ![0, 0, 0, 1], endpoint := ![![1, 1], ![1, 1], ![0, 1]], genus := ![0, 0] }
        :
        StableGraphCode.Candidate (Fin 4) 2 3).toGraph (g := 2) (by decide +kernel),
    kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
    halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }

/-- Balanced lookup of the decorated columns in the retained candidate vectors. -/
def graph : Fin 815 → DecoratedStableGraph (Fin 4) :=
  (fun i ↦ (if i.val < 407 then (if i.val < 203 then (if i.val < 101 then (if i.val < 50 then
    (if i.val < 25 then (if i.val < 12 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1
    then graph0 else (if i.val < 2 then graph1 else graph2)) else (if i.val < 4 then graph3 else
    (if i.val < 5 then graph4 else graph5))) else (if i.val < 9 then (if i.val < 7 then graph6
    else (if i.val < 8 then graph7 else graph8)) else (if i.val < 10 then graph9 else (if i.val
    < 11 then graph10 else graph11)))) else (if i.val < 18 then (if i.val < 15 then (if i.val <
    13 then graph12 else (if i.val < 14 then graph13 else graph14)) else (if i.val < 16 then
    graph15 else (if i.val < 17 then graph16 else graph17))) else (if i.val < 21 then (if i.val
    < 19 then graph18 else (if i.val < 20 then graph19 else graph20)) else (if i.val < 23 then
    (if i.val < 22 then graph21 else graph22) else (if i.val < 24 then graph23 else graph24)))))
    else (if i.val < 37 then (if i.val < 31 then (if i.val < 28 then (if i.val < 26 then graph25
    else (if i.val < 27 then graph26 else graph27)) else (if i.val < 29 then graph28 else (if
    i.val < 30 then graph29 else graph30))) else (if i.val < 34 then (if i.val < 32 then graph31
    else (if i.val < 33 then graph32 else graph33)) else (if i.val < 35 then graph34 else (if
    i.val < 36 then graph35 else graph36)))) else (if i.val < 43 then (if i.val < 40 then (if
    i.val < 38 then graph37 else (if i.val < 39 then graph38 else graph39)) else (if i.val < 41
    then graph40 else (if i.val < 42 then graph41 else graph42))) else (if i.val < 46 then (if
    i.val < 44 then graph43 else (if i.val < 45 then graph44 else graph45)) else (if i.val < 48
    then (if i.val < 47 then graph46 else graph47) else (if i.val < 49 then graph48 else
    graph49)))))) else (if i.val < 75 then (if i.val < 62 then (if i.val < 56 then (if i.val <
    53 then (if i.val < 51 then graph50 else (if i.val < 52 then graph51 else graph52)) else (if
    i.val < 54 then graph53 else (if i.val < 55 then graph54 else graph55))) else (if i.val < 59
    then (if i.val < 57 then graph56 else (if i.val < 58 then graph57 else graph58)) else (if
    i.val < 60 then graph59 else (if i.val < 61 then graph60 else graph61)))) else (if i.val <
    68 then (if i.val < 65 then (if i.val < 63 then graph62 else (if i.val < 64 then graph63
    else graph64)) else (if i.val < 66 then graph65 else (if i.val < 67 then graph66 else
    graph67))) else (if i.val < 71 then (if i.val < 69 then graph68 else (if i.val < 70 then
    graph69 else graph70)) else (if i.val < 73 then (if i.val < 72 then graph71 else graph72)
    else (if i.val < 74 then graph73 else graph74))))) else (if i.val < 88 then (if i.val < 81
    then (if i.val < 78 then (if i.val < 76 then graph75 else (if i.val < 77 then graph76 else
    graph77)) else (if i.val < 79 then graph78 else (if i.val < 80 then graph79 else graph80)))
    else (if i.val < 84 then (if i.val < 82 then graph81 else (if i.val < 83 then graph82 else
    graph83)) else (if i.val < 86 then (if i.val < 85 then graph84 else graph85) else (if i.val
    < 87 then graph86 else graph87)))) else (if i.val < 94 then (if i.val < 91 then (if i.val <
    89 then graph88 else (if i.val < 90 then graph89 else graph90)) else (if i.val < 92 then
    graph91 else (if i.val < 93 then graph92 else graph93))) else (if i.val < 97 then (if i.val
    < 95 then graph94 else (if i.val < 96 then graph95 else graph96)) else (if i.val < 99 then
    (if i.val < 98 then graph97 else graph98) else (if i.val < 100 then graph99 else
    graph100))))))) else (if i.val < 152 then (if i.val < 126 then (if i.val < 113 then (if
    i.val < 107 then (if i.val < 104 then (if i.val < 102 then graph101 else (if i.val < 103
    then graph102 else graph103)) else (if i.val < 105 then graph104 else (if i.val < 106 then
    graph105 else graph106))) else (if i.val < 110 then (if i.val < 108 then graph107 else (if
    i.val < 109 then graph108 else graph109)) else (if i.val < 111 then graph110 else (if i.val
    < 112 then graph111 else graph112)))) else (if i.val < 119 then (if i.val < 116 then (if
    i.val < 114 then graph113 else (if i.val < 115 then graph114 else graph115)) else (if i.val
    < 117 then graph116 else (if i.val < 118 then graph117 else graph118))) else (if i.val < 122
    then (if i.val < 120 then graph119 else (if i.val < 121 then graph120 else graph121)) else
    (if i.val < 124 then (if i.val < 123 then graph122 else graph123) else (if i.val < 125 then
    graph124 else graph125))))) else (if i.val < 139 then (if i.val < 132 then (if i.val < 129
    then (if i.val < 127 then graph126 else (if i.val < 128 then graph127 else graph128)) else
    (if i.val < 130 then graph129 else (if i.val < 131 then graph130 else graph131))) else (if
    i.val < 135 then (if i.val < 133 then graph132 else (if i.val < 134 then graph133 else
    graph134)) else (if i.val < 137 then (if i.val < 136 then graph135 else graph136) else (if
    i.val < 138 then graph137 else graph138)))) else (if i.val < 145 then (if i.val < 142 then
    (if i.val < 140 then graph139 else (if i.val < 141 then graph140 else graph141)) else (if
    i.val < 143 then graph142 else (if i.val < 144 then graph143 else graph144))) else (if i.val
    < 148 then (if i.val < 146 then graph145 else (if i.val < 147 then graph146 else graph147))
    else (if i.val < 150 then (if i.val < 149 then graph148 else graph149) else (if i.val < 151
    then graph150 else graph151)))))) else (if i.val < 177 then (if i.val < 164 then (if i.val <
    158 then (if i.val < 155 then (if i.val < 153 then graph152 else (if i.val < 154 then
    graph153 else graph154)) else (if i.val < 156 then graph155 else (if i.val < 157 then
    graph156 else graph157))) else (if i.val < 161 then (if i.val < 159 then graph158 else (if
    i.val < 160 then graph159 else graph160)) else (if i.val < 162 then graph161 else (if i.val
    < 163 then graph162 else graph163)))) else (if i.val < 170 then (if i.val < 167 then (if
    i.val < 165 then graph164 else (if i.val < 166 then graph165 else graph166)) else (if i.val
    < 168 then graph167 else (if i.val < 169 then graph168 else graph169))) else (if i.val < 173
    then (if i.val < 171 then graph170 else (if i.val < 172 then graph171 else graph172)) else
    (if i.val < 175 then (if i.val < 174 then graph173 else graph174) else (if i.val < 176 then
    graph175 else graph176))))) else (if i.val < 190 then (if i.val < 183 then (if i.val < 180
    then (if i.val < 178 then graph177 else (if i.val < 179 then graph178 else graph179)) else
    (if i.val < 181 then graph180 else (if i.val < 182 then graph181 else graph182))) else (if
    i.val < 186 then (if i.val < 184 then graph183 else (if i.val < 185 then graph184 else
    graph185)) else (if i.val < 188 then (if i.val < 187 then graph186 else graph187) else (if
    i.val < 189 then graph188 else graph189)))) else (if i.val < 196 then (if i.val < 193 then
    (if i.val < 191 then graph190 else (if i.val < 192 then graph191 else graph192)) else (if
    i.val < 194 then graph193 else (if i.val < 195 then graph194 else graph195))) else (if i.val
    < 199 then (if i.val < 197 then graph196 else (if i.val < 198 then graph197 else graph198))
    else (if i.val < 201 then (if i.val < 200 then graph199 else graph200) else (if i.val < 202
    then graph201 else graph202)))))))) else (if i.val < 305 then (if i.val < 254 then (if i.val
    < 228 then (if i.val < 215 then (if i.val < 209 then (if i.val < 206 then (if i.val < 204
    then graph203 else (if i.val < 205 then graph204 else graph205)) else (if i.val < 207 then
    graph206 else (if i.val < 208 then graph207 else graph208))) else (if i.val < 212 then (if
    i.val < 210 then graph209 else (if i.val < 211 then graph210 else graph211)) else (if i.val
    < 213 then graph212 else (if i.val < 214 then graph213 else graph214)))) else (if i.val <
    221 then (if i.val < 218 then (if i.val < 216 then graph215 else (if i.val < 217 then
    graph216 else graph217)) else (if i.val < 219 then graph218 else (if i.val < 220 then
    graph219 else graph220))) else (if i.val < 224 then (if i.val < 222 then graph221 else (if
    i.val < 223 then graph222 else graph223)) else (if i.val < 226 then (if i.val < 225 then
    graph224 else graph225) else (if i.val < 227 then graph226 else graph227))))) else (if i.val
    < 241 then (if i.val < 234 then (if i.val < 231 then (if i.val < 229 then graph228 else (if
    i.val < 230 then graph229 else graph230)) else (if i.val < 232 then graph231 else (if i.val
    < 233 then graph232 else graph233))) else (if i.val < 237 then (if i.val < 235 then graph234
    else (if i.val < 236 then graph235 else graph236)) else (if i.val < 239 then (if i.val < 238
    then graph237 else graph238) else (if i.val < 240 then graph239 else graph240)))) else (if
    i.val < 247 then (if i.val < 244 then (if i.val < 242 then graph241 else (if i.val < 243
    then graph242 else graph243)) else (if i.val < 245 then graph244 else (if i.val < 246 then
    graph245 else graph246))) else (if i.val < 250 then (if i.val < 248 then graph247 else (if
    i.val < 249 then graph248 else graph249)) else (if i.val < 252 then (if i.val < 251 then
    graph250 else graph251) else (if i.val < 253 then graph252 else graph253)))))) else (if
    i.val < 279 then (if i.val < 266 then (if i.val < 260 then (if i.val < 257 then (if i.val <
    255 then graph254 else (if i.val < 256 then graph255 else graph256)) else (if i.val < 258
    then graph257 else (if i.val < 259 then graph258 else graph259))) else (if i.val < 263 then
    (if i.val < 261 then graph260 else (if i.val < 262 then graph261 else graph262)) else (if
    i.val < 264 then graph263 else (if i.val < 265 then graph264 else graph265)))) else (if
    i.val < 272 then (if i.val < 269 then (if i.val < 267 then graph266 else (if i.val < 268
    then graph267 else graph268)) else (if i.val < 270 then graph269 else (if i.val < 271 then
    graph270 else graph271))) else (if i.val < 275 then (if i.val < 273 then graph272 else (if
    i.val < 274 then graph273 else graph274)) else (if i.val < 277 then (if i.val < 276 then
    graph275 else graph276) else (if i.val < 278 then graph277 else graph278))))) else (if i.val
    < 292 then (if i.val < 285 then (if i.val < 282 then (if i.val < 280 then graph279 else (if
    i.val < 281 then graph280 else graph281)) else (if i.val < 283 then graph282 else (if i.val
    < 284 then graph283 else graph284))) else (if i.val < 288 then (if i.val < 286 then graph285
    else (if i.val < 287 then graph286 else graph287)) else (if i.val < 290 then (if i.val < 289
    then graph288 else graph289) else (if i.val < 291 then graph290 else graph291)))) else (if
    i.val < 298 then (if i.val < 295 then (if i.val < 293 then graph292 else (if i.val < 294
    then graph293 else graph294)) else (if i.val < 296 then graph295 else (if i.val < 297 then
    graph296 else graph297))) else (if i.val < 301 then (if i.val < 299 then graph298 else (if
    i.val < 300 then graph299 else graph300)) else (if i.val < 303 then (if i.val < 302 then
    graph301 else graph302) else (if i.val < 304 then graph303 else graph304))))))) else (if
    i.val < 356 then (if i.val < 330 then (if i.val < 317 then (if i.val < 311 then (if i.val <
    308 then (if i.val < 306 then graph305 else (if i.val < 307 then graph306 else graph307))
    else (if i.val < 309 then graph308 else (if i.val < 310 then graph309 else graph310))) else
    (if i.val < 314 then (if i.val < 312 then graph311 else (if i.val < 313 then graph312 else
    graph313)) else (if i.val < 315 then graph314 else (if i.val < 316 then graph315 else
    graph316)))) else (if i.val < 323 then (if i.val < 320 then (if i.val < 318 then graph317
    else (if i.val < 319 then graph318 else graph319)) else (if i.val < 321 then graph320 else
    (if i.val < 322 then graph321 else graph322))) else (if i.val < 326 then (if i.val < 324
    then graph323 else (if i.val < 325 then graph324 else graph325)) else (if i.val < 328 then
    (if i.val < 327 then graph326 else graph327) else (if i.val < 329 then graph328 else
    graph329))))) else (if i.val < 343 then (if i.val < 336 then (if i.val < 333 then (if i.val
    < 331 then graph330 else (if i.val < 332 then graph331 else graph332)) else (if i.val < 334
    then graph333 else (if i.val < 335 then graph334 else graph335))) else (if i.val < 339 then
    (if i.val < 337 then graph336 else (if i.val < 338 then graph337 else graph338)) else (if
    i.val < 341 then (if i.val < 340 then graph339 else graph340) else (if i.val < 342 then
    graph341 else graph342)))) else (if i.val < 349 then (if i.val < 346 then (if i.val < 344
    then graph343 else (if i.val < 345 then graph344 else graph345)) else (if i.val < 347 then
    graph346 else (if i.val < 348 then graph347 else graph348))) else (if i.val < 352 then (if
    i.val < 350 then graph349 else (if i.val < 351 then graph350 else graph351)) else (if i.val
    < 354 then (if i.val < 353 then graph352 else graph353) else (if i.val < 355 then graph354
    else graph355)))))) else (if i.val < 381 then (if i.val < 368 then (if i.val < 362 then (if
    i.val < 359 then (if i.val < 357 then graph356 else (if i.val < 358 then graph357 else
    graph358)) else (if i.val < 360 then graph359 else (if i.val < 361 then graph360 else
    graph361))) else (if i.val < 365 then (if i.val < 363 then graph362 else (if i.val < 364
    then graph363 else graph364)) else (if i.val < 366 then graph365 else (if i.val < 367 then
    graph366 else graph367)))) else (if i.val < 374 then (if i.val < 371 then (if i.val < 369
    then graph368 else (if i.val < 370 then graph369 else graph370)) else (if i.val < 372 then
    graph371 else (if i.val < 373 then graph372 else graph373))) else (if i.val < 377 then (if
    i.val < 375 then graph374 else (if i.val < 376 then graph375 else graph376)) else (if i.val
    < 379 then (if i.val < 378 then graph377 else graph378) else (if i.val < 380 then graph379
    else graph380))))) else (if i.val < 394 then (if i.val < 387 then (if i.val < 384 then (if
    i.val < 382 then graph381 else (if i.val < 383 then graph382 else graph383)) else (if i.val
    < 385 then graph384 else (if i.val < 386 then graph385 else graph386))) else (if i.val < 390
    then (if i.val < 388 then graph387 else (if i.val < 389 then graph388 else graph389)) else
    (if i.val < 392 then (if i.val < 391 then graph390 else graph391) else (if i.val < 393 then
    graph392 else graph393)))) else (if i.val < 400 then (if i.val < 397 then (if i.val < 395
    then graph394 else (if i.val < 396 then graph395 else graph396)) else (if i.val < 398 then
    graph397 else (if i.val < 399 then graph398 else graph399))) else (if i.val < 403 then (if
    i.val < 401 then graph400 else (if i.val < 402 then graph401 else graph402)) else (if i.val
    < 405 then (if i.val < 404 then graph403 else graph404) else (if i.val < 406 then graph405
    else graph406))))))))) else (if i.val < 611 then (if i.val < 509 then (if i.val < 458 then
    (if i.val < 432 then (if i.val < 419 then (if i.val < 413 then (if i.val < 410 then (if
    i.val < 408 then graph407 else (if i.val < 409 then graph408 else graph409)) else (if i.val
    < 411 then graph410 else (if i.val < 412 then graph411 else graph412))) else (if i.val < 416
    then (if i.val < 414 then graph413 else (if i.val < 415 then graph414 else graph415)) else
    (if i.val < 417 then graph416 else (if i.val < 418 then graph417 else graph418)))) else (if
    i.val < 425 then (if i.val < 422 then (if i.val < 420 then graph419 else (if i.val < 421
    then graph420 else graph421)) else (if i.val < 423 then graph422 else (if i.val < 424 then
    graph423 else graph424))) else (if i.val < 428 then (if i.val < 426 then graph425 else (if
    i.val < 427 then graph426 else graph427)) else (if i.val < 430 then (if i.val < 429 then
    graph428 else graph429) else (if i.val < 431 then graph430 else graph431))))) else (if i.val
    < 445 then (if i.val < 438 then (if i.val < 435 then (if i.val < 433 then graph432 else (if
    i.val < 434 then graph433 else graph434)) else (if i.val < 436 then graph435 else (if i.val
    < 437 then graph436 else graph437))) else (if i.val < 441 then (if i.val < 439 then graph438
    else (if i.val < 440 then graph439 else graph440)) else (if i.val < 443 then (if i.val < 442
    then graph441 else graph442) else (if i.val < 444 then graph443 else graph444)))) else (if
    i.val < 451 then (if i.val < 448 then (if i.val < 446 then graph445 else (if i.val < 447
    then graph446 else graph447)) else (if i.val < 449 then graph448 else (if i.val < 450 then
    graph449 else graph450))) else (if i.val < 454 then (if i.val < 452 then graph451 else (if
    i.val < 453 then graph452 else graph453)) else (if i.val < 456 then (if i.val < 455 then
    graph454 else graph455) else (if i.val < 457 then graph456 else graph457)))))) else (if
    i.val < 483 then (if i.val < 470 then (if i.val < 464 then (if i.val < 461 then (if i.val <
    459 then graph458 else (if i.val < 460 then graph459 else graph460)) else (if i.val < 462
    then graph461 else (if i.val < 463 then graph462 else graph463))) else (if i.val < 467 then
    (if i.val < 465 then graph464 else (if i.val < 466 then graph465 else graph466)) else (if
    i.val < 468 then graph467 else (if i.val < 469 then graph468 else graph469)))) else (if
    i.val < 476 then (if i.val < 473 then (if i.val < 471 then graph470 else (if i.val < 472
    then graph471 else graph472)) else (if i.val < 474 then graph473 else (if i.val < 475 then
    graph474 else graph475))) else (if i.val < 479 then (if i.val < 477 then graph476 else (if
    i.val < 478 then graph477 else graph478)) else (if i.val < 481 then (if i.val < 480 then
    graph479 else graph480) else (if i.val < 482 then graph481 else graph482))))) else (if i.val
    < 496 then (if i.val < 489 then (if i.val < 486 then (if i.val < 484 then graph483 else (if
    i.val < 485 then graph484 else graph485)) else (if i.val < 487 then graph486 else (if i.val
    < 488 then graph487 else graph488))) else (if i.val < 492 then (if i.val < 490 then graph489
    else (if i.val < 491 then graph490 else graph491)) else (if i.val < 494 then (if i.val < 493
    then graph492 else graph493) else (if i.val < 495 then graph494 else graph495)))) else (if
    i.val < 502 then (if i.val < 499 then (if i.val < 497 then graph496 else (if i.val < 498
    then graph497 else graph498)) else (if i.val < 500 then graph499 else (if i.val < 501 then
    graph500 else graph501))) else (if i.val < 505 then (if i.val < 503 then graph502 else (if
    i.val < 504 then graph503 else graph504)) else (if i.val < 507 then (if i.val < 506 then
    graph505 else graph506) else (if i.val < 508 then graph507 else graph508))))))) else (if
    i.val < 560 then (if i.val < 534 then (if i.val < 521 then (if i.val < 515 then (if i.val <
    512 then (if i.val < 510 then graph509 else (if i.val < 511 then graph510 else graph511))
    else (if i.val < 513 then graph512 else (if i.val < 514 then graph513 else graph514))) else
    (if i.val < 518 then (if i.val < 516 then graph515 else (if i.val < 517 then graph516 else
    graph517)) else (if i.val < 519 then graph518 else (if i.val < 520 then graph519 else
    graph520)))) else (if i.val < 527 then (if i.val < 524 then (if i.val < 522 then graph521
    else (if i.val < 523 then graph522 else graph523)) else (if i.val < 525 then graph524 else
    (if i.val < 526 then graph525 else graph526))) else (if i.val < 530 then (if i.val < 528
    then graph527 else (if i.val < 529 then graph528 else graph529)) else (if i.val < 532 then
    (if i.val < 531 then graph530 else graph531) else (if i.val < 533 then graph532 else
    graph533))))) else (if i.val < 547 then (if i.val < 540 then (if i.val < 537 then (if i.val
    < 535 then graph534 else (if i.val < 536 then graph535 else graph536)) else (if i.val < 538
    then graph537 else (if i.val < 539 then graph538 else graph539))) else (if i.val < 543 then
    (if i.val < 541 then graph540 else (if i.val < 542 then graph541 else graph542)) else (if
    i.val < 545 then (if i.val < 544 then graph543 else graph544) else (if i.val < 546 then
    graph545 else graph546)))) else (if i.val < 553 then (if i.val < 550 then (if i.val < 548
    then graph547 else (if i.val < 549 then graph548 else graph549)) else (if i.val < 551 then
    graph550 else (if i.val < 552 then graph551 else graph552))) else (if i.val < 556 then (if
    i.val < 554 then graph553 else (if i.val < 555 then graph554 else graph555)) else (if i.val
    < 558 then (if i.val < 557 then graph556 else graph557) else (if i.val < 559 then graph558
    else graph559)))))) else (if i.val < 585 then (if i.val < 572 then (if i.val < 566 then (if
    i.val < 563 then (if i.val < 561 then graph560 else (if i.val < 562 then graph561 else
    graph562)) else (if i.val < 564 then graph563 else (if i.val < 565 then graph564 else
    graph565))) else (if i.val < 569 then (if i.val < 567 then graph566 else (if i.val < 568
    then graph567 else graph568)) else (if i.val < 570 then graph569 else (if i.val < 571 then
    graph570 else graph571)))) else (if i.val < 578 then (if i.val < 575 then (if i.val < 573
    then graph572 else (if i.val < 574 then graph573 else graph574)) else (if i.val < 576 then
    graph575 else (if i.val < 577 then graph576 else graph577))) else (if i.val < 581 then (if
    i.val < 579 then graph578 else (if i.val < 580 then graph579 else graph580)) else (if i.val
    < 583 then (if i.val < 582 then graph581 else graph582) else (if i.val < 584 then graph583
    else graph584))))) else (if i.val < 598 then (if i.val < 591 then (if i.val < 588 then (if
    i.val < 586 then graph585 else (if i.val < 587 then graph586 else graph587)) else (if i.val
    < 589 then graph588 else (if i.val < 590 then graph589 else graph590))) else (if i.val < 594
    then (if i.val < 592 then graph591 else (if i.val < 593 then graph592 else graph593)) else
    (if i.val < 596 then (if i.val < 595 then graph594 else graph595) else (if i.val < 597 then
    graph596 else graph597)))) else (if i.val < 604 then (if i.val < 601 then (if i.val < 599
    then graph598 else (if i.val < 600 then graph599 else graph600)) else (if i.val < 602 then
    graph601 else (if i.val < 603 then graph602 else graph603))) else (if i.val < 607 then (if
    i.val < 605 then graph604 else (if i.val < 606 then graph605 else graph606)) else (if i.val
    < 609 then (if i.val < 608 then graph607 else graph608) else (if i.val < 610 then graph609
    else graph610)))))))) else (if i.val < 713 then (if i.val < 662 then (if i.val < 636 then
    (if i.val < 623 then (if i.val < 617 then (if i.val < 614 then (if i.val < 612 then graph611
    else (if i.val < 613 then graph612 else graph613)) else (if i.val < 615 then graph614 else
    (if i.val < 616 then graph615 else graph616))) else (if i.val < 620 then (if i.val < 618
    then graph617 else (if i.val < 619 then graph618 else graph619)) else (if i.val < 621 then
    graph620 else (if i.val < 622 then graph621 else graph622)))) else (if i.val < 629 then (if
    i.val < 626 then (if i.val < 624 then graph623 else (if i.val < 625 then graph624 else
    graph625)) else (if i.val < 627 then graph626 else (if i.val < 628 then graph627 else
    graph628))) else (if i.val < 632 then (if i.val < 630 then graph629 else (if i.val < 631
    then graph630 else graph631)) else (if i.val < 634 then (if i.val < 633 then graph632 else
    graph633) else (if i.val < 635 then graph634 else graph635))))) else (if i.val < 649 then
    (if i.val < 642 then (if i.val < 639 then (if i.val < 637 then graph636 else (if i.val < 638
    then graph637 else graph638)) else (if i.val < 640 then graph639 else (if i.val < 641 then
    graph640 else graph641))) else (if i.val < 645 then (if i.val < 643 then graph642 else (if
    i.val < 644 then graph643 else graph644)) else (if i.val < 647 then (if i.val < 646 then
    graph645 else graph646) else (if i.val < 648 then graph647 else graph648)))) else (if i.val
    < 655 then (if i.val < 652 then (if i.val < 650 then graph649 else (if i.val < 651 then
    graph650 else graph651)) else (if i.val < 653 then graph652 else (if i.val < 654 then
    graph653 else graph654))) else (if i.val < 658 then (if i.val < 656 then graph655 else (if
    i.val < 657 then graph656 else graph657)) else (if i.val < 660 then (if i.val < 659 then
    graph658 else graph659) else (if i.val < 661 then graph660 else graph661)))))) else (if
    i.val < 687 then (if i.val < 674 then (if i.val < 668 then (if i.val < 665 then (if i.val <
    663 then graph662 else (if i.val < 664 then graph663 else graph664)) else (if i.val < 666
    then graph665 else (if i.val < 667 then graph666 else graph667))) else (if i.val < 671 then
    (if i.val < 669 then graph668 else (if i.val < 670 then graph669 else graph670)) else (if
    i.val < 672 then graph671 else (if i.val < 673 then graph672 else graph673)))) else (if
    i.val < 680 then (if i.val < 677 then (if i.val < 675 then graph674 else (if i.val < 676
    then graph675 else graph676)) else (if i.val < 678 then graph677 else (if i.val < 679 then
    graph678 else graph679))) else (if i.val < 683 then (if i.val < 681 then graph680 else (if
    i.val < 682 then graph681 else graph682)) else (if i.val < 685 then (if i.val < 684 then
    graph683 else graph684) else (if i.val < 686 then graph685 else graph686))))) else (if i.val
    < 700 then (if i.val < 693 then (if i.val < 690 then (if i.val < 688 then graph687 else (if
    i.val < 689 then graph688 else graph689)) else (if i.val < 691 then graph690 else (if i.val
    < 692 then graph691 else graph692))) else (if i.val < 696 then (if i.val < 694 then graph693
    else (if i.val < 695 then graph694 else graph695)) else (if i.val < 698 then (if i.val < 697
    then graph696 else graph697) else (if i.val < 699 then graph698 else graph699)))) else (if
    i.val < 706 then (if i.val < 703 then (if i.val < 701 then graph700 else (if i.val < 702
    then graph701 else graph702)) else (if i.val < 704 then graph703 else (if i.val < 705 then
    graph704 else graph705))) else (if i.val < 709 then (if i.val < 707 then graph706 else (if
    i.val < 708 then graph707 else graph708)) else (if i.val < 711 then (if i.val < 710 then
    graph709 else graph710) else (if i.val < 712 then graph711 else graph712))))))) else (if
    i.val < 764 then (if i.val < 738 then (if i.val < 725 then (if i.val < 719 then (if i.val <
    716 then (if i.val < 714 then graph713 else (if i.val < 715 then graph714 else graph715))
    else (if i.val < 717 then graph716 else (if i.val < 718 then graph717 else graph718))) else
    (if i.val < 722 then (if i.val < 720 then graph719 else (if i.val < 721 then graph720 else
    graph721)) else (if i.val < 723 then graph722 else (if i.val < 724 then graph723 else
    graph724)))) else (if i.val < 731 then (if i.val < 728 then (if i.val < 726 then graph725
    else (if i.val < 727 then graph726 else graph727)) else (if i.val < 729 then graph728 else
    (if i.val < 730 then graph729 else graph730))) else (if i.val < 734 then (if i.val < 732
    then graph731 else (if i.val < 733 then graph732 else graph733)) else (if i.val < 736 then
    (if i.val < 735 then graph734 else graph735) else (if i.val < 737 then graph736 else
    graph737))))) else (if i.val < 751 then (if i.val < 744 then (if i.val < 741 then (if i.val
    < 739 then graph738 else (if i.val < 740 then graph739 else graph740)) else (if i.val < 742
    then graph741 else (if i.val < 743 then graph742 else graph743))) else (if i.val < 747 then
    (if i.val < 745 then graph744 else (if i.val < 746 then graph745 else graph746)) else (if
    i.val < 749 then (if i.val < 748 then graph747 else graph748) else (if i.val < 750 then
    graph749 else graph750)))) else (if i.val < 757 then (if i.val < 754 then (if i.val < 752
    then graph751 else (if i.val < 753 then graph752 else graph753)) else (if i.val < 755 then
    graph754 else (if i.val < 756 then graph755 else graph756))) else (if i.val < 760 then (if
    i.val < 758 then graph757 else (if i.val < 759 then graph758 else graph759)) else (if i.val
    < 762 then (if i.val < 761 then graph760 else graph761) else (if i.val < 763 then graph762
    else graph763)))))) else (if i.val < 789 then (if i.val < 776 then (if i.val < 770 then (if
    i.val < 767 then (if i.val < 765 then graph764 else (if i.val < 766 then graph765 else
    graph766)) else (if i.val < 768 then graph767 else (if i.val < 769 then graph768 else
    graph769))) else (if i.val < 773 then (if i.val < 771 then graph770 else (if i.val < 772
    then graph771 else graph772)) else (if i.val < 774 then graph773 else (if i.val < 775 then
    graph774 else graph775)))) else (if i.val < 782 then (if i.val < 779 then (if i.val < 777
    then graph776 else (if i.val < 778 then graph777 else graph778)) else (if i.val < 780 then
    graph779 else (if i.val < 781 then graph780 else graph781))) else (if i.val < 785 then (if
    i.val < 783 then graph782 else (if i.val < 784 then graph783 else graph784)) else (if i.val
    < 787 then (if i.val < 786 then graph785 else graph786) else (if i.val < 788 then graph787
    else graph788))))) else (if i.val < 802 then (if i.val < 795 then (if i.val < 792 then (if
    i.val < 790 then graph789 else (if i.val < 791 then graph790 else graph791)) else (if i.val
    < 793 then graph792 else (if i.val < 794 then graph793 else graph794))) else (if i.val < 798
    then (if i.val < 796 then graph795 else (if i.val < 797 then graph796 else graph797)) else
    (if i.val < 800 then (if i.val < 799 then graph798 else graph799) else (if i.val < 801 then
    graph800 else graph801)))) else (if i.val < 808 then (if i.val < 805 then (if i.val < 803
    then graph802 else (if i.val < 804 then graph803 else graph804)) else (if i.val < 806 then
    graph805 else (if i.val < 807 then graph806 else graph807))) else (if i.val < 811 then (if
    i.val < 809 then graph808 else (if i.val < 810 then graph809 else graph810)) else (if i.val
    < 813 then (if i.val < 812 then graph811 else graph812) else (if i.val < 814 then graph813
    else graph814)))))))))))

/-- Every raw column is a stable genus-two graph. -/
theorem graph_totalGenus (i : Fin 815) : (graph i).graph.totalGenus = 2 := by
  revert i
  decide +kernel

/-- Quotient columns retain the held finite presentations. -/
def columns (i : Fin 815) : TautologicalStratum 2 (Fin 4) :=
  .mk (graph i) (graph_totalGenus i)

/-- All columns are kappa-free and have codimension three. -/
theorem graph_degree : ∀ i, (graph i).codimension = 3 ∧ (graph i).kappaCodimension = 0 := by
  decide +kernel

end AxiomaticGW.L24Graphs
