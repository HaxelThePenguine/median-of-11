"""Exercise arbitrary orientation and the deletion bijection, including ties."""
from itertools import permutations, product

def execute(gates, values):
    values = list(values)
    for low, high in gates:
        values[low], values[high] = sorted((values[low], values[high]))
    return values

def delete(gates, missing, sentinel):
    # Physical port -> persistent ordinary-wire label. None denotes the hole.
    labels = list(range(3))
    labels.insert(missing, None)
    reduced = []
    for low, high in gates:
        if None in (labels[low], labels[high]):
            if (labels[low] is None) != (sentinel < 0):
                labels[low], labels[high] = labels[high], labels[low]
        else:
            reduced.append((labels[low], labels[high]))
    return reduced, labels

def check():
    ports = list(permutations(range(4),2))
    assignments = list(product(range(3), repeat=3))
    cases = 0
    for length in range(4):
        for gates in product(ports, repeat=length):
            for missing, sentinel in product(range(4), (-1,3)):
                reduced, labels = delete(gates, missing, sentinel)
                for x in assignments:
                    full = list(x)
                    full.insert(missing, sentinel)
                    y = execute(reduced, x)
                    expected = [sentinel if label is None else y[label] for label in labels]
                    if execute(gates, full) != expected:
                        raise ValueError((gates, missing, sentinel, x))
                    cases += 1
    print(f"{cases} full-vector deletion comparisons passed")

if __name__ == "__main__":
    check()
