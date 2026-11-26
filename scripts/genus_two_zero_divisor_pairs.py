"""Recognize the empty-singleton-table marked divisor equation on validated blowup queries."""


def accepts(query):
    """Mirror zeroDivisorPair? for the CLI's normalized [label, psi] insertion lists."""
    marks = query["insertions"]
    if query["target"] not in ("X1", "X2") or query["genus"] != 2 or len(marks) != 2:
        return False
    for index, (label, power) in enumerate(marks):
        if label == "unit" and (power == 1 or (power == 0 and marks[1 - index][1] > 0)):
            return False
    beta = query["class"]
    for index, (divisor, power) in enumerate(marks):
        if divisor in ("unit", "pt") or power != 0:
            continue
        survivor, survivor_power = marks[1 - index]
        intersection = beta[-1]
        if divisor != "H":
            intersection -= beta[int(divisor[1:]) - 1]
        cup_zero = survivor_power == 0 or survivor not in ("unit", divisor)
        return intersection == 0 and cup_zero
    return False
