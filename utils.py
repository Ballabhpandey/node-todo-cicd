
TIME_OUT = 120

from os.path import exists
import re
from subprocess import check_output

from latest.idp_engine import IDP, Theory, Assignments

def get_content(file):
    with open(file, 'r') as f:
        out = f.read()
    return out

def set_content(file, content):
    mode = "w" if exists(file) else "x"
    with open(file, mode) as stream:
        stream.write(content)

def run (f, th: str, cli:bool, verify : bool = False):
    if "1.idp" in f:
        th = th + """
procedure main() {
    logging.getLogger().setLevel(logging.INFO)
    interp, sol = Theory(T).generate(timeout_seconds=0, unsat_seconds=0)
    pretty_print(sol)
    print(duration("Expansion"))
    print("-------------------")
    print(Theory(T).expand_lifting(sol))
    print("-------------------")
}
        """

    elif "2.idp" in f:
        th = th + """
procedure main() {
    logging.getLogger().setLevel(logging.INFO)
    interp, sol = Theory(T).generate(factor=1.5, timeout_seconds=0, unsat_seconds=0)
    pretty_print(sol)
    print(duration("Expansion"))
    print("-------------------")
    print(Theory(T).expand_lifting(sol))
    print("-------------------")
}
        """

    else:
        assert False, "Can't determine which program to use"

    set_content(f, th)
    if cli:
        cmd = f"poetry run python3.10 ./latest/idp-engine.py {f}"
        try:
            out = check_output(cmd.split(" "), timeout=TIME_OUT).decode("utf-8")
        except Exception as e:
            out = " T  " + str(e)

        set_content(f.replace(".idp", ".out"), out)
        if " T  " not in out:
            m = re.search('(\d+.\d+) Expansion', out)
            duration = m.group(0).split(" ")[0]
            duration = duration[:duration.find(".")+3]  # 2 decimals
            if verify:
                struct = out.split("-------------------")[1]
                cth = get_content(f.replace(".l_", "."))
                cth = cth.split("procedure")[0]
                th = cth + f"structure S:V {{{struct}}}" + """
procedure main() {
    pretty_print(Theory(T, S).expand(max=1))
}
                """
                kb = IDP.from_str(th)
                T, S = kb.get_blocks("T, S")
                out = next(Theory(T, S).expand(max=1))
                assert type(out) == Assignments, f"Incorrect theory: {th} {type(out)}"
            return duration
        return " T  "
    elif "1.idp" in f:
        kb = IDP.from_str(th)
        T = kb.get_blocks("T")[0]
        interp, out = Theory(T).generate(timeout_seconds=TIME_OUT)
        set_content(f.replace(".idp", ".out"), str(out))
    else:
        kb = IDP.from_str(th)
        T = kb.get_blocks("T")[0]
        interp, out = Theory(T).generate(factor=1.5, timeout_seconds=TIME_OUT)
        set_content(f.replace(".idp", ".out"), str(out))
    return out

def problem(f, n):
    source = get_content(f)
    kb = IDP.from_str(source.replace("$n$", str(n)))
    T, S = kb.get_blocks("T, S")
    out = Theory(T, S, extended=True)
    return out

def monotype1(f, problem, cli=True):
    CT, CTth = problem.transform(monotype=True, lift=False)
    new_f = f.replace("concrete.idp", "monotype1.idp")
    return run(new_f, CT, cli)

def monotype2(f, problem, cli=True):
    CT, CTth = problem.transform(monotype=True, factor=1.5, lift=False)
    new_f = f.replace("concrete.idp", "monotype2.idp")
    return run(new_f, CT, cli)

def type1(f, problem, cli=True):
    CT, CTth = problem.transform(lift=False)
    new_f = f.replace("concrete.idp", "type1.idp")
    return run(new_f, CT, cli)

def type2(f, problem, cli=True):
    CT, CTth = problem.transform(factor=1.5, lift=False)
    new_f = f.replace("concrete.idp", "type2.idp")
    return run(new_f, CT, cli)

def l_monotype1(f, problem, cli=True):
    CT, CTth = problem.transform(monotype=True, lift=True)
    new_f = f.replace("concrete.idp", "l_monotype1.idp")
    return run(new_f, CT, cli, verify=True)

def l_monotype2(f, problem, cli=True):
    CT, CTth = problem.transform(factor=1.5, monotype=True, lift=True)
    new_f = f.replace("concrete.idp", "l_monotype2.idp")
    return run(new_f, CT, cli, verify=True)

def l_type1(f, problem, cli=True):
    CT, CTth = problem.transform(lift=True)
    new_f = f.replace("concrete.idp", "l_type1.idp")
    return run(new_f, CT, cli, verify=True)

def l_type2(f, problem, cli=True):
    CT, CTth = problem.transform(factor=1.5, lift=True)
    new_f = f.replace("concrete.idp", "l_type2.idp")
    return run(new_f, CT, cli, verify=True)