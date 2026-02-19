#!/usr/bin/env python3
import sys
import pathlib

from svabench.pyverilog.vparser.ast import InstanceList
from svabench.pyverilog.vparser.parser import parse_
from svabench.pyverilog.vparser.preprocessor import pp


def top_mod_score(
    hierarchy: dict[str, list[str]], mod: str, db: dict[str, int]
) -> int:
    """
    Computes a "score" based on the size of the children instances inside a
    module
    Adapted from https://github.com/YosysHQ/yosys/passes/hierarchy/hierarchy.cc
    """
    if mod not in db:
        score = 0
        db[mod] = 0
        if len(hierarchy[mod]) == 0:
            return 0
        for child in hierarchy[mod]:
            score = max(score, (top_mod_score(hierarchy, child, db) + 1))
        db[mod] = score
    return db[mod]


def top(hierarchy: dict[str, list[str]]) -> str | None:
    """
    Return the top module given a design hierarchy
    Top Module is defined as the module that is not instantiated in any other
    module and has atleast one child(in case of multiple modules).
    If multiple top modules are present then the root of the deepest tree is
    chosen
    """
    # Handle the case of a singleton
    ret = next(iter(hierarchy))
    db: dict[str, int] = dict()
    max_num_children = top_mod_score(hierarchy, ret, db)
    for k in hierarchy:
        is_instantiated = False
        for k_ in hierarchy:
            if k != k_:
                is_instantiated |= k in hierarchy[k_]
        # Not in any other module and has modules of its own
        if len(hierarchy[k]) != 0 and not is_instantiated:
            if top_mod_score(hierarchy, k, db) > max_num_children:
                max_num_children = top_mod_score(hierarchy, k, db)
                ret = k
    print(db)
    return ret


def main():
    commandfile = pathlib.Path(sys.argv[1]).resolve()
    preprocessed_text = pp(str(commandfile))
    ast = parse_(preprocessed_text)
    hierarchy: dict[str, list[str]] = {}
    for module in ast.description.children():
        hierarchy[module.name] = list()
        for item in module.items:
            if type(item) == InstanceList:
                hierarchy[module.name].append(item.module)
    print("isolated")
    for k in hierarchy:
        is_instantiated = False
        for k_ in hierarchy:
            if k != k_:
                is_instantiated |= k in hierarchy[k_]
        if len(hierarchy[k]) == 0 and not is_instantiated:
            print("\t", k)
    print("Top", top(hierarchy))
    return


if __name__ == "__main__":
    main()
