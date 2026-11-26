#!/usr/bin/env python3
"""Replay every L24 correction against independently held Lean graph operations.

The producer and parser are outside the proof boundary. The graph frame and
context descriptions are pinned to the held definitions; exact row equality
is proved by the Lean kernel. This file does not assume class vanishing from
an intersection diagnostic. The initial BP expression requires a separate realized-class replay.
"""
import argparse
import hashlib
from fractions import Fraction
import json
from pathlib import Path
import textwrap
from export_admcycles_certificate import integer, rational, rational_vector, require, unique_object
from export_genus_two_psi_pullbacks import SOURCE_PINS, PRODUCER_PINS
from test_l24_normalization import key, pad, relabel, replace_raw

ROOT = Path(__file__).resolve().parents[1]

FRAME_IDS = [47, 48, 49, 50, 57, 58, 60, 68, 69, 71, 85, 88, 90, 93, 94, 101, 102, 103, 105, 112, 113, 114, 116, 129, 130, 131, 132, 133, 134, 137, 138, 145, 146, 148, 163, 164, 167, 170, 171, 185, 186, 189, 192, 193, 214, 219, 223, 226, 230, 231, 233, 234, 236, 237, 240, 241, 244, 246, 247, 249, 250, 252, 253, 260, 262, 263, 265, 266, 268, 269, 276, 279, 280, 281, 283, 285, 286, 288, 289, 292, 293, 296, 298, 299, 301, 302, 305, 306, 309, 312, 313, 314, 316, 318, 319, 321, 322, 329, 332, 333, 334, 336, 339, 340, 341, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 624, 625, 626, 627, 630, 631, 632, 633, 634, 637, 638, 639, 640, 641, 644, 645, 646, 647, 648, 650, 651, 653, 657, 658, 659, 660, 663, 664, 665, 667, 670, 672, 673, 674, 676, 677, 679, 683, 684, 685, 686, 689, 690, 691, 693, 696, 698, 699, 700, 703, 704, 705, 707, 708, 709, 714, 715, 717, 718, 719, 720, 722, 723, 724, 725, 728, 729, 730, 731, 732, 735, 736, 737, 738, 739, 742, 743, 744, 745, 746, 748, 749, 750, 751, 754, 755, 756, 757, 758, 761, 762, 763, 764, 765, 768, 769, 770, 771, 772, 775, 776, 777, 779, 780, 781, 785, 786, 787, 789, 790, 791, 792, 794, 795, 797, 801, 802, 803, 804, 807, 808, 809, 811, 814, 816, 817, 818, 821, 822, 823, 825, 826, 827, 831, 833, 835, 836, 837, 838, 841, 842, 843, 845, 846, 847, 851, 853, 855, 856, 857, 858, 861, 862, 863, 864, 870, 875, 880, 881, 884, 885, 888, 889, 890, 895, 898, 899, 904, 907, 908, 912, 913, 914, 917, 920, 926, 927, 930, 931, 935, 936, 939, 940, 944, 945, 946, 949, 953, 957, 958, 962, 963, 964, 967, 971, 972, 973, 976, 979, 980, 981, 982, 986, 988, 989, 993, 995, 996, 1001, 1003, 1004, 1007, 1011, 1013, 1014, 1019, 1021, 1022, 1025, 1030, 1032, 1033, 1036, 1040, 1042, 1043, 1047, 1049, 1050, 1055, 1057, 1058, 1061, 1065, 1067, 1068, 1073, 1075, 1076, 1079, 1083, 1084, 1086, 1093, 1097, 1104, 1112, 1114, 1115, 1118, 1122, 1123, 1125, 1129, 1130, 1132, 1134, 1135, 1136, 1137, 1138, 1139, 1140, 1141, 1142, 1143, 1144, 1145, 1146, 1147, 1148, 1149, 1150, 1151, 1152, 1153, 1154, 1155, 1156, 1157, 1158, 1159, 1160, 1161, 1162, 1163, 1164, 1165, 1166, 1167, 1168, 1169, 1170, 1171, 1172, 1173, 1174, 1175, 1176, 1177, 1178, 1179, 1180, 1181, 1182, 1183, 1184, 1185, 1186, 1187, 1188, 1189, 1190, 1191, 1192, 1193, 1194, 1195, 1196, 1197, 1198, 1199, 1200, 1201, 1202, 1203, 1204, 1205, 1206, 1207, 1208, 1209, 1210, 1211, 1212, 1213, 1214, 1215, 1216, 1217, 1218, 1219, 1220, 1221, 1222, 1223, 1224, 1225, 1226, 1227, 1228, 1229, 1230, 1231, 1232, 1233, 1234, 1235, 1236, 1237, 1238, 1239, 1240, 1241, 1242, 1243, 1244, 1245, 1343, 1345, 1347, 1349, 1351, 1353, 1355, 1357, 1359, 1361, 1418, 1419, 1420, 1421, 1423, 1424, 1425, 1428, 1429, 1430, 1434, 1435, 1436, 1437, 1439, 1440, 1442, 1443, 1444, 1445, 1447, 1448, 1449, 1450, 1453, 1454, 1455, 1456, 1458, 1459, 1461, 1462, 1463, 1467, 1468, 1469, 1470, 1472, 1473, 1476, 1477, 1478, 1479, 1481, 1482, 1486, 1487, 1488, 1489, 1495, 1500, 1505, 1506, 1508, 1509, 1512, 1513, 1514, 1518, 1519, 1521, 1522, 1526, 1527, 1529, 1530, 1534, 1535, 1536, 1538, 1541, 1547, 1548, 1550, 1551, 1555, 1556, 1558, 1559, 1563, 1564, 1565, 1567, 1571, 1572, 1574, 1575, 1579, 1580, 1581, 1583, 1587, 1588, 1589, 1591, 1595, 1596, 1597, 1598, 1601, 1602, 1603, 1604, 1609, 1611, 1612, 1613, 1618, 1620, 1621, 1622, 1627, 1628, 1630, 1631, 1636, 1638, 1639, 1640, 1645, 1646, 1648, 1649, 1654, 1655, 1657, 1658, 1663, 1664, 1665, 1667, 1672, 1674, 1675, 1676, 1681, 1682, 1684, 1685, 1690, 1691, 1693, 1694, 1699, 1700, 1701, 1703, 1708, 1709, 1711, 1712, 1717, 1718, 1719, 1721, 1726, 1727, 1728, 1730, 1735, 1736, 1737, 1738, 1741, 1742, 1743, 1744, 1745, 1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753, 1754, 1755, 1756, 1757, 1758, 1759, 1760, 1761, 1762, 1763, 1764, 1765, 1766, 1767, 1768, 1769, 1770, 1771, 1772, 1773, 1774, 1775, 1776, 1777, 1778, 1779, 1780, 1781, 1782, 1783, 1784, 1785, 1786, 1787, 1788, 1789, 1790, 1791, 1792, 1793, 1794, 1795, 1796, 1797, 1798, 1799, 1800, 1801, 1802, 1803, 1804, 1805, 1806, 1807, 1808, 1809, 1810, 1811, 1812, 1813, 1814, 1815, 1816, 1817, 1818, 1819, 1820, 1821, 1822, 1823, 1824, 1825, 1826, 1827, 1828, 1829, 1830, 1831, 1832, 1833, 1834, 1835, 1836, 1837, 1838, 1839, 1840, 1841, 1842, 1843, 1844, 1845, 1846, 1847, 1848, 1849, 1850, 1851, 1852, 1853, 1854, 1855, 1856, 1857, 1858, 1859, 1860, 1861, 1862, 1863, 1864, 1865, 1866, 1867, 1868, 1869, 1870, 1871, 1872, 1873, 1874, 1875, 1876, 1877, 1878, 1879, 1880, 1881, 1882, 1883, 2048, 2049, 2050, 2051, 2052, 2053, 2054, 2055, 2056, 2057]
FIELDS = {'permutations', 'scope', 'wdvv', 'producer_sha256', 'initial', 'schema_version', 'frame', 'graphs', 'source', 'source_sha256', 'normalization_scale', 'normalization', 'primitive', 'steps', 'intersection_diagnostics', 'full', 'native_substitution_checks', 'environment', 'pictures'}
GRAPH_SHA256 = 'd090bf7f9e5e5647a6232c3ca21f6c22b6021366032fe995f85393ffc35a2b58'
STEP_CONTEXT_SHA256 = '43ff7fe0ce240c5cf9bf3289883e038adfc4a76be40997c45e0bbb10886c4b92'
WDVV_CONTEXT_SHA256 = '04bde5d97b731758c62517b497996faddba792e43b9a95544b4918b4fd81284a'
PERMUTATIONS_SHA256 = '00d8032f4a48e5cf827315feb50fdf7157c1c1483f6a3b167448a6e04b753c34'
PICTURES_SHA256 = 'e9af94ae0ae689f3507d70e74b6e051a4d675491f544b55c07aaa4f2d21c182a'


def canonical_hash(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def dense(entries):
    require(isinstance(entries, list), "Expected sparse coordinates")
    result = [[0, 1] for _ in FRAME_IDS]
    lookup = {old: i for i, old in enumerate(FRAME_IDS)}
    previous = -1
    for term in entries:
        require(isinstance(term, list) and len(term) == 2, "Malformed sparse term")
        old, coefficient = term
        old = integer(old, "Invalid column index")
        require(old in lookup and old > previous, "Unknown, repeated or unsorted column")
        require(rational(coefficient) != 0, "Explicit sparse zero")
        result[lookup[old]] = coefficient
        previous = old
    return result


def balanced_coordinates(values):
    """Render exact coordinates with logarithmic kernel lookup depth."""
    terms = [str(p) if q == 1 else f"({p} / {q})" for p, q in values]

    def tree(start, stop):
        if all(t == terms[start] for t in terms[start:stop]):
            return terms[start]
        middle = (start + stop) // 2
        return (f"(if i.val < {middle} then {tree(start, middle)} "
                f"else {tree(middle, stop)})")

    return "fun i ↦ " + tree(0, len(terms))


def read_report(raw):
    r = json.loads(raw, object_pairs_hook=unique_object)
    require(isinstance(r, dict) and set(r) == FIELDS, "Invalid top-level fields")
    require(integer(r.get("schema_version"), "Invalid schema") == 1, "Wrong schema")
    require(r.get("frame") == "l24_direct_normalization_exploration_v1", "Wrong claim frame")
    require(r.get("environment") == {"sage": "10.9", "admcycles": "1.4"}, "Changed environment")
    require(r.get("normalization") == "raw_gluing_pushforward", "Changed normalization")
    require(rational(r.get("normalization_scale")) == 1 and
            r["normalization_scale"] == [1, 1], "Changed scale")
    require(r.get("source_sha256") == SOURCE_PINS and r.get("producer_sha256") == PRODUCER_PINS,
            "Changed source provenance")
    require(r.get("source") == "https://arxiv.org/html/2210.04038; sections 4 and 7.1",
            "Changed mathematical source")
    require(canonical_hash(r.get("permutations")) == PERMUTATIONS_SHA256,
            "Changed marking average")
    require(canonical_hash(r.get("pictures")) == PICTURES_SHA256,
            "Changed primitive target diagrams")
    require(canonical_hash(r.get("graphs")) == GRAPH_SHA256, "Changed graph frame")
    require(isinstance(r.get("steps"), list) and len(r["steps"]) == 66, "Missing correction")
    require(isinstance(r.get("wdvv"), list) and len(r["wdvv"]) == 5, "Missing WDVV correction")
    for label, expected in (("steps", STEP_CONTEXT_SHA256), ("wdvv", WDVV_CONTEXT_SHA256)):
        for step in r[label]:
            require(isinstance(step, dict) and "row" in step and "weight" in step,
                    "Malformed correction")
            rational(step["weight"])
            dense(step["row"])
        require(canonical_hash([{k: v for k, v in step.items() if k not in ("row", "weight")}
                                for step in r[label]]) == expected, "Changed correction context")
    for label in ("initial", "full", "primitive"):
        dense(r[label])
    return r


def high_record_hints(report):
    """Untrusted short arithmetic hints; Lean checks each pair against the held maps."""
    frames = {2: json.loads((ROOT / "environments/genus-two-psi-product-exploration.json").read_bytes()),
              3: json.loads((ROOT / "environments/belorousski-pandharipande.json").read_bytes())}
    pulls = json.loads((ROOT / "environments/genus-two-psi-pullbacks-exploration.json").read_bytes())
    coefficients = {("square", 2): pulls["cases"][0]["coordinates"],
                    ("square", 3): pulls["cases"][1]["coordinates"],
                    ("product", 3): pulls["cases"][2]["coordinates"],
                    ("product", 2): frames[2]["requested"]}
    columns = {key(report["graphs"][old]): i for i, old in enumerate(FRAME_IDS)}
    result = []
    for step in report["steps"][:29]:
        order = step["order"]
        n = len(order)
        inverse = [order.index(i) for i in range(n)]
        entries = []
        for c, graph in zip(coefficients[step["kind"], n], frames[n]["graphs"]):
            destination = 0 if c[0] == 0 else columns[key(replace_raw(
                report["graphs"][step["base"]], step["vertex"], relabel(pad(graph), inverse)))]
            coefficient = str(c[0]) if c[1] == 1 else f"({c[0]} / {c[1]})"
            entries.append(f"({destination}, {coefficient})")
        source = "GenusTwoPsiProduct.requested" if step["kind"] == "product" and n == 2 else (
            "GenusTwoPsiPullbacksReplay." + step["kind"] + ("TwoClaim" if n == 2 else "ThreeClaim"))
        result.append((f"L24HighPsi.destination{step['base']}", source,
                       "[" + ", ".join(entries) + "]"))
    return result


def complete_replay_source(raw):
    r = read_report(raw)
    hints = high_record_hints(r)
    out = ["/-", "Copyright (c) 2026 JMA. All rights reserved.",
           "Released under Apache 2.0 license as described in the file LICENSE.", "Authors: JMA",
           "-/", "module", "",
           "public import AxiomaticGW.Tautological.L24HighPsi",
           "public import AxiomaticGW.Tautological.L24RationalPsi",
           "public import AxiomaticGW.Tautological.L24WDVV", "",
           "public import AxiomaticGW.Tautological.StrataCoordinateRecords", "",
           "/-!", "# Exact incoming L24 correction coefficients", "",
           "Input SHA256: " + hashlib.sha256(raw).hexdigest(),
           "All 71 contextual rows are compared to actual independently held Lean operations.",
           "The initial BP coordinate claim is separate and requires its own graph replay.",
           "-/", "", "@[expose] public section", "",
           "namespace AxiomaticGW.L24CorrectionsReplay",
           "open RelationCertificate StrataOperation", "",
           "set_option maxRecDepth 20000", ""]
    families = (("high", "L24HighPsi", r["steps"][:29]),
                ("rational", "L24RationalPsi", r["steps"][29:]),
                ("wdvv", "L24WDVV", r["wdvv"]))
    def row(name, entries):
        out.extend(["/-- Incoming exact raw coordinates; validity is checked separately. -/",
                    f"def {name} : Coordinates 815 :=",
                    textwrap.fill(balanced_coordinates(dense(entries)), width=96, initial_indent="  ",
                                  subsequent_indent="    "), ""])
    for family, ns, steps in families:
        for j, step in enumerate(steps):
            row(f"{family}{j}", step["row"])
            if family == "high":
                destination, source, entries = hints[j]
                out += ["/-- Untrusted ordered coefficient records; zero entries are retained. -/",
                        f"def high{j}Records : List (Fin 815 × ℚ) :=",
                        textwrap.fill(entries, width=96, initial_indent="  ", subsequent_indent="    "),
                        "", "/-- Every finite record is bound to the actual source and destination. -/",
                        f"theorem high{j}Records_checked : imageRecords",
                        f"    {destination} {source} = high{j}Records := by",
                        "  decide +kernel", ""]
            out += ["/-- The full incoming row agrees with its actual contextual source image. -/",
                    f"theorem {family}{j}_checked : {ns}.correctionCoordinates {j} = {family}{j} := by"]
            if family == "high":
                out += [f"  change imageCoordinates {destination}",
                        f"    {source} = _",
                        f"  rw [imageCoordinates_eq_records, high{j}Records_checked]"]
            out += ["  decide +kernel", ""]
        count = len(steps)
        out += ["/-- All checked incoming rows, in their retained source-operation order. -/",
                f"def {family}Rows : Fin {count} → Coordinates 815 :=",
                textwrap.fill("![" + ", ".join(f"{family}{j}" for j in range(count)) + "]",
                              width=96, initial_indent="  ", subsequent_indent="    "), "",
                "/-- Exact chosen rational weights; the final sum is checked below. -/",
                f"def {family}Weights : Fin {count} → ℚ :=",
                textwrap.fill(rational_vector([step["weight"] for step in steps]), width=96,
                              initial_indent="  ", subsequent_indent="    "), "",
                "/-- Every row in this complete family has been replayed. -/",
                f"theorem {family}_checked (i : Fin {count}) :",
                f"    {ns}.correctionCoordinates i = {family}Rows i := by", "  fin_cases i"]
        out += [f"  · exact {family}{j}_checked" for j in range(count)] + [""]
    for label in ("initial", "full", "primitive"):
        row(label + "Claim", r[label])
    before = [Fraction(*q) for q in dense(r["initial"])]
    for step in r["steps"]:
        for j, q in enumerate(dense(step["row"])):
            before[j] += Fraction(*step["weight"]) * Fraction(*q)
    row("beforeAverageClaim", [[old, [q.numerator, q.denominator]]
        for old, q in zip(FRAME_IDS, before) if q])
    out += ["/-- The unaveraged correction sum is checked before finite label averaging. -/",
            "theorem beforeAverage_checked : initialClaim +",
            "    (∑ i, highWeights i • highRows i) + (∑ i, rationalWeights i • rationalRows i) =",
            "    beforeAverageClaim := by", "  apply funext", "  intro j",
            "  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,",
            "    Fin.sum_univ_succ, Fin.sum_univ_zero, highWeights, highRows,",
            "    rationalWeights, rationalRows, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]",
            "  revert j", "  decide +kernel", ""]
    out += ["/-- The exact complete correction sum, including its final marking average. -/",
            "def assembled : Coordinates 815 :=",
            "  L24Symmetry.averageCoordinates (initialClaim +",
            "    (∑ i, highWeights i • highRows i) + (∑ i, rationalWeights i • rationalRows i)) +",
            "    ∑ i, wdvvWeights i • wdvvRows i", "",
            "/-- Kernel arithmetic checks the complete 721-term candidate. -/",
            "theorem assembled_checked : assembled = fullClaim := by",
            "  rw [assembled, beforeAverage_checked]", "  apply funext", "  intro j",
            "  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]",
            "  revert j", "  decide +kernel", "",
            "end AxiomaticGW.L24CorrectionsReplay", ""]
    return "\n".join(out)


def replay_sources(raw):
    """Keep independently checkable families in separate compilation units."""
    source = complete_replay_source(raw)
    marker = "/-- Incoming exact raw coordinates; validity is checked separately. -/"
    positions = [source.rfind(marker, 0, source.index(f"def {name}"))
                 for name in ("high0 :", "rational0 :", "wdvv0 :", "initialClaim :")]
    header = source[:positions[0]]
    end = "end AxiomaticGW.L24CorrectionsReplay\n"
    outputs = {}
    families = (("High", "L24HighPsi"), ("Rational", "L24RationalPsi"), ("WDVV", "L24WDVV"))
    for index, (name, dependency) in enumerate(families):
        imports = {"public import AxiomaticGW.Tautological." + dependency}
        if name == "High":
            imports.add("public import AxiomaticGW.Tautological.StrataCoordinateRecords")
        own_header = "\n".join(line for line in header.splitlines()
                               if not line.startswith("public import ") or line in imports) + "\n"
        outputs[f"L24{name}CorrectionsReplay.lean"] = (
            own_header + source[positions[index]:positions[index + 1]] + end)
    own_header = "\n".join(line for line in header.splitlines()
                           if not line.startswith("public import ")) + "\n"
    claims_end = source.index("/-- The unaveraged correction sum is checked before finite label averaging. -/")
    claims_header = own_header.replace("module\n", "module\n\npublic import "
        "AxiomaticGW.Tautological.RelationCertificate\n", 1)
    claims_header = claims_header.replace("open RelationCertificate StrataOperation",
                                          "open RelationCertificate")
    claims_header = claims_header.replace("# Exact incoming L24 correction coefficients",
                                          "# Held L24 coordinate claims")
    claims_header = claims_header.replace(
        "All 71 contextual rows are compared to actual independently held Lean operations.",
        "These are coefficient data only; L24CorrectionsReplay checks the complete assembly.")
    outputs["L24Claims.lean"] = claims_header + source[positions[3]:claims_end] + end
    imports = "public import AxiomaticGW.Tautological.Fixtures.L24Claims\n" + "\n".join(
        "public import AxiomaticGW.Tautological.Fixtures.L24" + name +
                        "CorrectionsReplay" for name, _ in families)
    own_header = own_header.replace("module\n", "module\n\n" + imports + "\n", 1)
    outputs["L24CorrectionsReplay.lean"] = own_header + source[claims_end:]
    return outputs


def replay_source(raw):
    return replay_sources(raw)["L24CorrectionsReplay.lean"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    sources = replay_sources(args.input.read_bytes())
    for name, source in sources.items():
        output = args.output if name == "L24CorrectionsReplay.lean" else args.output.with_name(name)
        if args.check:
            require(output.read_text() == source, "Stored replay differs: " + name)
        else:
            output.write_text(source)


if __name__ == "__main__":
    main()
