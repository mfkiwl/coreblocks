Search.setIndex({"docnames": ["Assumptions", "Development_environment", "Home", "Problem-checklist", "Transactions", "api", "coreblocks", "coreblocks.frontend", "coreblocks.fu", "coreblocks.params", "coreblocks.peripherals", "coreblocks.scheduler", "coreblocks.stages", "coreblocks.structs_common", "coreblocks.transactions", "coreblocks.utils", "index", "modules", "scheduler/Overview", "shared_structs/Implementation/RS_impl", "shared_structs/RS"], "filenames": ["Assumptions.md", "Development_environment.md", "Home.md", "Problem-checklist.md", "Transactions.md", "api.md", "coreblocks.rst", "coreblocks.frontend.rst", "coreblocks.fu.rst", "coreblocks.params.rst", "coreblocks.peripherals.rst", "coreblocks.scheduler.rst", "coreblocks.stages.rst", "coreblocks.structs_common.rst", "coreblocks.transactions.rst", "coreblocks.utils.rst", "index.md", "modules.rst", "scheduler/Overview.md", "shared_structs/Implementation/RS_impl.md", "shared_structs/RS.md"], "titles": ["List of assumptions made during development", "Development environment", "Introduction", "Problem checklist", "Documentation for Coreblocks transaction framework", "API", "coreblocks package", "coreblocks.frontend package", "coreblocks.fu package", "coreblocks.params package", "coreblocks.peripherals package", "coreblocks.scheduler package", "coreblocks.stages package", "coreblocks.structs_common package", "coreblocks.transactions package", "coreblocks.utils package", "Coreblocks", "coreblocks", "Scheduler overview", "Proposition of Reservation Station implementation", "Reservation Station"], "terms": {"rf": [0, 5, 6, 12, 17, 19, 20], "ha": [0, 3, 14, 19], "data": [0, 10, 14, 16, 20], "forward": 0, "from": [0, 3, 4, 10, 12, 14, 19, 20], "tomasulo": 0, "announc": [0, 12], "bu": [0, 9, 10], "read": [0, 3, 4, 10, 14, 16], "x0": 0, "rf0": 0, "return": [0, 4, 10, 14, 15], "0": [0, 6, 7, 8, 9, 10, 11, 12, 13, 14, 19, 20], "write": [0, 3, 4, 14, 20], "i": [0, 2, 4, 9, 10, 12, 14, 15, 18, 19, 20], "noop": 0, "separ": [0, 14, 18], "r": [0, 1, 5, 6, 9, 12, 17, 18, 19, 20], "each": [0, 9, 10, 14, 16, 19, 20], "fu": [0, 5, 6, 12, 17, 19, 20], "writeback": 0, "stage": [0, 5, 6, 17], "save": [0, 12, 19, 20], "rob": [0, 5, 6, 12, 17, 18, 19, 20], "after": [0, 10, 18], "get": [0, 12, 14, 15, 16], "output": [0, 10, 12, 14, 19, 20], "commit": [0, 1], "updat": 0, "rat": [0, 5, 6, 17], "In": [1, 2, 4, 14, 20], "order": [1, 2], "prepar": 1, "pleas": [1, 3, 4, 9], "follow": [1, 4, 15, 19], "step": [1, 4], "below": 1, "instal": 1, "python": [1, 4, 14], "3": [1, 9, 15], "10": [1, 9], "interpret": 1, "pip": 1, "packag": [1, 5, 17], "manag": [1, 14], "option": [1, 4, 9, 14, 15], "creat": [1, 14], "virtual": 1, "python3": 1, "m": [1, 4, 9, 14, 15], "venv": 1, "project": [1, 2], "directori": [1, 2], "activ": [1, 14], "us": [1, 3, 4, 10, 12, 14, 15, 16], "gener": [1, 3, 10, 12, 14, 15], "script": 1, "bin": 1, "all": [1, 3, 4, 9, 14, 15, 16], "requir": [1, 14], "librari": [1, 14, 16], "pip3": 1, "dev": 1, "txt": 1, "precommit": 1, "hook": 1, "pre": 1, "coreblock": 2, "go": [2, 3, 14], "an": [2, 3, 4, 9, 12, 14, 15, 19], "out": [2, 14], "processor": [2, 18], "which": [2, 4, 12, 14, 15, 18, 19, 20], "implement": [2, 16, 18], "risc": [2, 9], "v": [2, 9, 19], "microarchitectur": 2, "The": [2, 10, 12, 14, 15, 16, 18, 19, 20], "focu": 2, "flexibl": [2, 18], "should": [2, 4, 10, 12, 14, 18, 19, 20], "allow": [2, 14, 15], "easili": [2, 14], "make": [2, 3], "experi": 2, "differ": [2, 3, 12, 14], "compon": [2, 14], "locat": [2, 18], "doc": 2, "collect": 2, "descript": [2, 16], "whole": 2, "overview": [2, 16], "high": 2, "level": 2, "can": [2, 4, 12, 14, 15, 18, 19], "found": 2, "If": [3, 4, 10, 14, 15, 19], "someth": [3, 4], "doesn": 3, "t": [3, 14, 15, 19], "work": [3, 4], "you": [3, 19], "re": [3, 4, 10], "puzzl": 3, "why": 3, "through": 3, "thi": [3, 4, 10, 12, 14, 15, 19, 20], "see": [3, 4], "ani": 3, "point": 3, "appli": 3, "your": 3, "case": [3, 10, 12, 15], "sure": 3, "yield": 3, "when": [3, 4, 10, 14, 19, 20], "call": [3, 4, 14, 19], "function": [3, 4, 14, 15], "test": [3, 14, 15], "e": [3, 9, 14], "g": 3, "testbenchio": 3, "notabl": 3, "except": [3, 12, 15], "settl": 3, "instead": 3, "signal": [3, 10, 14, 15, 16], "unexpect": 3, "valu": [3, 9, 12, 14, 15, 19, 20], "try": [3, 4], "ad": [3, 14], "right": 3, "befor": [3, 18], "don": [3, 19], "do": 3, "eq": [3, 4, 14], "two": [3, 4, 12, 14], "record": [3, 4, 10, 14, 15], "layout": [3, 4, 5, 6, 10, 12, 14, 15, 17], "have": [3, 12, 14, 15], "painstakingli": 3, "everi": [3, 10, 14], "": [3, 4, 9, 10, 14], "field": [3, 9, 12, 14, 15, 19, 20], "amaranth": [3, 4, 10, 14, 15], "statement": [3, 4, 15], "ar": [3, 4, 10, 12, 14, 15, 18, 19, 20], "some": [3, 4, 14], "domain": [3, 14], "check": [3, 15, 19, 20], "code": [3, 4, 14, 15], "combin": [3, 14], "loop": 3, "especi": 3, "simul": [3, 14], "hang": 3, "extend": 3, "list": [3, 10, 14, 16], "spot": 3, "yourself": [3, 4], "easi": [3, 4], "fix": 3, "mistak": 3, "util": [4, 5, 6, 17], "modular": 4, "design": 4, "It": [4, 12, 14, 18, 19], "inspir": 4, "bluespec": 4, "program": 4, "languag": 4, "wiki": 4, "compil": 4, "idea": 4, "interfac": [4, 10, 14, 16], "hardwar": [4, 18], "modul": [4, 5, 17], "A": [4, 9, 14], "state": [4, 10, 14, 16], "chang": [4, 14, 19], "oper": [4, 14], "perform": [4, 14, 15], "singl": [4, 14, 15], "clock": [4, 14, 18], "cycl": [4, 14, 18], "atom": [4, 19], "given": [4, 14, 19], "either": [4, 14, 15], "execut": [4, 10, 12, 14, 18, 20], "its": [4, 12, 14], "entrieti": 4, "onli": [4, 14, 15], "readi": [4, 10, 12, 14, 16, 19], "doe": 4, "conflict": [4, 14], "anoth": [4, 14], "schedul": [4, 5, 6, 14, 16, 17], "same": [4, 14, 15], "defin": [4, 14, 15], "depend": [4, 9, 15], "other": [4, 14], "via": [4, 14], "directli": [4, 14], "link": 4, "indirectli": [4, 14], "multipl": [4, 10, 14], "one": [4, 10, 12, 14, 15, 18, 19, 20], "them": [4, 14, 15], "wai": [4, 14], "access": 4, "coordin": 4, "system": [4, 9], "avoid": 4, "commun": [4, 19], "caller": [4, 14], "both": [4, 14, 15, 19], "direct": [4, 14], "back": 4, "structur": [4, 16, 19], "simplest": 4, "part": [4, 14, 18], "elaborat": [4, 6, 7, 8, 10, 11, 12, 13, 14], "block": [4, 14, 16], "class": [4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], "myth": 4, "def": [4, 14], "elabor": 4, "self": 4, "platform": 4, "bodi": [4, 14], "condit": [4, 14], "includ": [4, 14, 15], "assign": [4, 14, 15], "like": [4, 10, 14], "d": [4, 9, 14], "comb": [4, 14], "sig1": 4, "expr1": 4, "sync": 4, "sig2": 4, "expr2": 4, "also": [4, 12], "result": [4, 10, 12, 14], "arg_expr": 4, "analog": 4, "multiplex": 4, "rememb": 4, "insid": [4, 14], "alwai": [4, 14], "onc": [4, 14], "exampl": [4, 14, 15, 19], "becaus": [4, 14], "resourc": [4, 14], "request": [4, 10, 14], "paramet": [4, 9, 10, 12, 14, 15], "bit": [4, 10, 15, 19, 20], "express": 4, "pass": [4, 12, 14], "expr": 4, "As": 4, "thei": [4, 10, 14, 18], "typic": [4, 14], "declar": 4, "constructor": [4, 14], "myotherth": 4, "__init__": 4, "o": [4, 14], "format": [4, 14, 15], "argument": [4, 10, 14, 20], "my_method": 4, "input_layout": 4, "output_layout": 4, "def_method": [4, 14], "_": [4, 14], "arg": [4, 6, 7, 8, 10, 11, 12, 13, 14], "other_method": 4, "ret_expr": 4, "techniqu": 4, "present": [4, 14, 15], "abov": 4, "conveni": [4, 14], "syntax": [4, 14], "just": 4, "particular": 4, "unnam": 4, "usual": 4, "For": [4, 9, 15, 19, 20], "could": 4, "around": 4, "entir": 4, "sometim": 4, "might": 4, "altern": 4, "decid": [4, 18], "best": 4, "import": 4, "question": 4, "ask": 4, "run": [4, 14], "independ": 4, "thing": 4, "lock": 4, "so": [4, 10, 12, 14], "mayb": 4, "Or": 4, "extern": [4, 14, 16], "doubt": 4, "prefer": 4, "need": [4, 10, 14, 19], "noth": 4, "els": 4, "Such": 4, "name": [4, 14, 15], "adaptertran": [4, 14], "facilit": 4, "contain": [4, 14, 15], "provid": [4, 9, 14], "most": [4, 14], "ones": 4, "connecttran": [4, 14], "connect": [4, 10, 12, 14], "togeth": 4, "fifo": [4, 12, 14], "queue": [4, 14], "adapt": [4, 14], "plain": [4, 14], "These": 4, "veri": 4, "testbench": [4, 14], "subpackag": [5, 17], "frontend": [5, 6, 17, 18], "submodul": [5, 17], "decod": [5, 6, 17], "fetch": [5, 6, 12, 17], "content": [5, 17], "alu": [5, 6, 17], "param": [5, 6, 17], "genparam": [5, 6, 12, 17], "isa": [5, 6, 17], "peripher": [5, 6, 17], "wishbon": [5, 6, 17], "wakeup_select": [5, 6, 17], "backend": [5, 6, 17], "retir": [5, 6, 17], "structs_common": [5, 6, 17], "transact": [5, 6, 10, 16, 17, 19], "core": [5, 12, 17], "lib": [5, 6, 17], "src_loc_at": [6, 7, 8, 10, 11, 12, 13, 14], "kwarg": [6, 7, 8, 10, 11, 12, 13, 14], "base": [6, 7, 8, 9, 10, 11, 12, 13, 14, 15], "instrdecod": 7, "alufuncunit": 8, "isa_str": 9, "str": [9, 14, 15], "phys_regs_bit": 9, "int": [9, 10, 14, 15], "7": 9, "rob_entries_bit": 9, "8": [9, 10, 14], "rs_entri": 9, "4": 9, "start_pc": 9, "dependentcach": 9, "extens": 9, "intflag": 9, "enumer": [9, 15], "c": 9, "64": [9, 10], "32": 9, "1": [9, 14, 15, 19, 20], "f": 9, "16": [9, 14], "2": [9, 10, 15], "zicsr": 9, "256": 9, "zifencei": 9, "128": 9, "fencefm": 9, "intenum": 9, "none": [9, 14, 15], "tso": 9, "fencetarget": 9, "dev_i": 9, "dev_o": 9, "mem_r": 9, "mem_w": 9, "funct12": 9, "ebreak": 9, "ecal": 9, "mret": 9, "770": 9, "wfi": 9, "261": 9, "funct3": 9, "add": [9, 14], "AND": 9, "b": 9, "beq": 9, "bge": 9, "5": [9, 18], "bgeu": 9, "blt": 9, "bltu": 9, "6": 9, "bne": 9, "csrrc": 9, "csrrci": 9, "csrr": 9, "csrrsi": 9, "csrrw": 9, "csrrwi": 9, "fenc": 9, "fencei": 9, "h": 9, "hu": 9, "jalr": 9, "OR": 9, "priv": 9, "sll": 9, "slt": 9, "sltu": 9, "sr": 9, "sub": 9, "w": 9, "xor": 9, "funct7": 9, "sa": 9, "sl": 9, "object": [9, 10, 14], "gather": 9, "specif": 9, "configur": 9, "numer": 9, "val": 9, "correspond": [9, 14, 19], "val_log": 9, "relev": 9, "string": 9, "identifi": [9, 19], "refer": 9, "gcc": 9, "machin": 9, "arch": 9, "detail": [9, 16], "attribut": [9, 10, 14], "xlen": 9, "nativ": 9, "integ": 9, "regist": [9, 14, 18], "width": [9, 10, 15], "reg_cnt": 9, "number": [9, 10, 14], "ilen": 9, "maximum": 9, "instruct": [9, 12, 16, 18, 19], "length": 9, "csr_alen": 9, "csr": 9, "address": [9, 10], "support": [9, 14], "form": 9, "bitwis": 9, "instrtyp": 9, "enum": [9, 14, 15], "j": 9, "u": 9, "optyp": 9, "arithmet": 9, "auipc": 9, "branch": 9, "compar": [9, 16], "12": 9, "11": 9, "15": 9, "jump": 9, "load": 9, "logic": [9, 14, 20], "13": 9, "shift": 9, "store": [9, 12, 14, 19, 20], "9": 9, "unknown": 9, "14": 9, "opcod": [9, 19, 20], "24": 9, "jal": 9, "27": 9, "25": 9, "lui": 9, "misc_mem": 9, "op": 9, "op_imm": 9, "28": 9, "commonlayout": 9, "gen_param": 9, "decodelayout": 9, "gen": [9, 12], "fetchlayout": 9, "funcunitlayout": 9, "ratlayout": 9, "rflayout": 9, "roblayout": 9, "rslayout": 9, "schedulerlayout": 9, "wishbonearbit": 10, "arbit": 10, "master": 10, "slave": 10, "assert": 10, "cyc": 10, "grant": [10, 14], "round": [10, 14], "robin": [10, 14], "manner": 10, "slavewb": 10, "wishbonelayout": 10, "intefac": 10, "wb_param": 10, "wishboneparamet": 10, "true": [10, 15], "boolean": 10, "whether": [10, 15], "side": [10, 19, 20], "otherwis": 10, "wb_layout": 10, "wishbonemast": 10, "wbmaster": 10, "method": [10, 12, 14, 16], "start": [10, 14], "new": [10, 14, 16], "being": [10, 15], "previou": 10, "take": [10, 12, 14, 18, 19], "requestlayout": 10, "becom": 10, "complet": [10, 12], "error": [10, 15], "success": 10, "resultlayout": 10, "generate_layout": 10, "wishbonememoryslav": 10, "memori": [10, 14], "underneath": 10, "dict": [10, 14], "keyword": 10, "underli": 10, "depth": [10, 14], "specifi": [10, 20], "infer": [10, 14], "data_width": 10, "addr_width": 10, "wishbonemux": 10, "muxer": 10, "masterwb": 10, "wisbon": 10, "sseltga": 10, "select": 10, "corespond": 10, "wisnon": 10, "tga": 10, "tag": [10, 12, 19, 20], "valid": [10, 19], "time": [10, 14], "stb": 10, "granular": 10, "paramt": 10, "dat_r": 10, "dat_w": 10, "default": [10, 14, 15], "adr": 10, "singal": 10, "smallest": 10, "unit": [10, 12, 18], "transfer": [10, 14], "port": [10, 14], "capabl": 10, "wakeupselect": 11, "resultannounc": 12, "simpl": [12, 14, 15], "send": 12, "mark": [12, 16], "sent": 12, "wait": [12, 14, 19, 20], "get_result": [12, 14], "alreadi": 12, "serial": 12, "we": [12, 18, 19, 20], "more": [12, 14, 16], "than": 12, "manytooneconnecttran": [12, 14], "instanc": [12, 14], "invok": [12, 19], "next": 12, "assum": [12, 15], "rob_mark_don": 12, "end": [12, 14], "without": 12, "rob_id": 12, "rs_write_v": 12, "finish": 12, "rf_write_v": 12, "reg_id": 12, "reg_val": 12, "frat": 13, "rrat": 13, "registerfil": 13, "reorderbuff": 13, "union": [14, 15], "sequenc": 14, "tupl": 14, "shape": 14, "rang": 14, "type": 14, "layoutlik": 14, "serv": 14, "simultena": 14, "transactionmanag": 14, "rest": 14, "must": 14, "combinatori": 14, "between": 14, "place": [14, 19], "data_out": 14, "data_in": 14, "describ": 14, "effect": [14, 19, 20], "hint": 14, "variabl": [14, 15], "current": 14, "add_conflict": 14, "cannot": 14, "simultan": 14, "reason": 14, "common": [14, 15], "hdl": [14, 15], "dsl": 14, "ast": [14, 15], "valuecast": [14, 15], "const": 14, "d1": 14, "d0": 14, "iter": [14, 15], "ret": 14, "user": 14, "feed": 14, "intern": [14, 16], "indic": [14, 20], "By": 14, "my_sum_method": 14, "arg1": 14, "arg2": 14, "sum": 14, "debug_sign": 14, "debugsign": 14, "map": [14, 15], "static": 14, "construct": 14, "input": [14, 19, 20], "blueprint": 14, "freshli": 14, "use_method": 14, "enabl": 14, "repres": 14, "task": [14, 18], "regularli": 14, "done": 14, "last": 14, "set": [14, 19], "met": 14, "concurr": 14, "explicit": 14, "implicit": 14, "aris": 14, "pair": 14, "wa": 14, "where": [14, 19, 20], "control": 14, "omit": 14, "receiv": 14, "transactioncontext": 14, "want": [14, 19], "inform": 14, "context": 14, "action": 14, "under": 14, "guard": 14, "classmethod": 14, "stack": 14, "respons": 14, "care": 14, "never": 14, "add_transact": 14, "transactionmodul": 14, "wrapper": 14, "handl": 14, "definit": 14, "wrap": 14, "decor": 14, "eleg": 14, "dictionari": 14, "whose": 14, "eager_deterministic_cc_schedul": 14, "gr": 14, "cc": 14, "eager": 14, "subsystem": 14, "isn": 14, "fair": 14, "index": [14, 15], "prioriti": 14, "lowest": 14, "highest": 14, "arbitr": 14, "agent": 14, "calcul": 14, "graph": 14, "vertic": 14, "edg": 14, "trivial_roundrobin_cc_schedul": 14, "even": 14, "non": [14, 19], "mainli": 14, "purpos": 14, "adapterbas": 14, "One": [14, 15], "possibl": [14, 15], "mock": 14, "en": 14, "expos": 14, "ifac": 14, "cattran": 14, "concaten": 14, "third": 14, "src1": [14, 20], "first": [14, 19, 20], "src2": [14, 20], "second": [14, 19, 20], "dst": 14, "clickin": 14, "click": 14, "interact": 14, "fpga": 14, "button": 14, "switch": [14, 15, 19], "On": 14, "rise": 14, "synchron": 14, "btn": 14, "dat": 14, "retriev": 14, "accept": 14, "empti": 14, "clickout": 14, "led": 14, "put": [14, 19], "vice": 14, "versa": 14, "compat": 14, "method1": 14, "method2": 14, "respect": 14, "full": 14, "fulfil": 14, "size": 14, "fifotyp": 14, "conform": 14, "syncfifo": 14, "mani": 14, "equival": 14, "put_result": 14, "method_us": 14, "assigntyp": 15, "rh": 15, "onehotswitch": 15, "hot": 15, "match": [15, 19, 20], "style": 15, "similar": 15, "standard": 15, "benefit": 15, "represent": 15, "sig": 15, "onehotcas": 15, "0b01": 15, "0b10": 15, "onehotswitchdynam": 15, "liter": 15, "fals": 15, "dynam": 15, "bool": 15, "signifi": 15, "lh": 15, "rec": 15, "assignfield": 15, "safe": 15, "report": 15, "mismatch": 15, "castabl": 15, "determin": 15, "rais": 15, "kei": 15, "item": 15, "subrecord": 15, "valueerror": 15, "introduct": 16, "document": 16, "assumpt": 16, "made": 16, "dure": [16, 18], "develop": 16, "environ": 16, "framework": [16, 19], "basic": 16, "usag": 16, "schema": 16, "proposit": 16, "reserv": 16, "station": 16, "actual": 16, "slot": 16, "tabl": 16, "substitut": 16, "row": 16, "clean": 16, "free": [16, 20], "reset": 16, "initi": 16, "insert": [16, 18, 19], "vector": 16, "problem": 16, "checklist": 16, "middl": 18, "our": 18, "Its": 18, "main": 18, "alloc": [18, 19, 20], "renam": 18, "entri": [18, 19, 20], "dispatch": [18, 19, 20], "rss": 18, "split": 18, "phase": 18, "choos": 18, "potenti": 18, "merg": 18, "futur": [18, 19], "optim": 18, "treat": 18, "todo": 18, "here": 19, "how": 19, "feel": 19, "anyth": 19, "buffer": 19, "id_out": [19, 20], "id_rob": [19, 20], "id_rs1": [19, 20], "val_rs1": [19, 20], "id_rs2": [19, 20], "val_rs2": [19, 20], "correct": [19, 20], "fill": 19, "operand": [19, 20], "id_rsx": 19, "sourc": 19, "appropri": 19, "val_rsx": 19, "zero": 19, "pipelin": 19, "releas": 19, "posit": [19, 20], "comparison": 19, "replac": 19, "null": [19, 20], "clear": [19, 20], "id": [19, 20], "woken": 20, "up": 20, "wakeup": 20, "invalid": 20, "inst_readi": 20, "long": 20, "mean": 20, "still": 20, "written": 20}, "objects": {"": [[6, 0, 0, "-", "coreblocks"]], "coreblocks": [[6, 0, 0, "-", "core"], [7, 0, 0, "-", "frontend"], [8, 0, 0, "-", "fu"], [9, 0, 0, "-", "params"], [10, 0, 0, "-", "peripherals"], [11, 0, 0, "-", "scheduler"], [12, 0, 0, "-", "stages"], [13, 0, 0, "-", "structs_common"], [14, 0, 0, "-", "transactions"], [15, 0, 0, "-", "utils"]], "coreblocks.core": [[6, 1, 1, "", "Core"]], "coreblocks.frontend": [[7, 0, 0, "-", "decode"], [7, 0, 0, "-", "decoder"], [7, 0, 0, "-", "fetch"]], "coreblocks.frontend.decode": [[7, 1, 1, "", "Decode"]], "coreblocks.frontend.decoder": [[7, 1, 1, "", "InstrDecoder"]], "coreblocks.frontend.fetch": [[7, 1, 1, "", "Fetch"]], "coreblocks.fu": [[8, 0, 0, "-", "alu"]], "coreblocks.fu.alu": [[8, 1, 1, "", "AluFuncUnit"]], "coreblocks.params": [[9, 0, 0, "-", "genparams"], [9, 0, 0, "-", "isa"], [9, 0, 0, "-", "layouts"]], "coreblocks.params.genparams": [[9, 1, 1, "", "GenParams"]], "coreblocks.params.isa": [[9, 1, 1, "", "Extension"], [9, 1, 1, "", "FenceFm"], [9, 1, 1, "", "FenceTarget"], [9, 1, 1, "", "Funct12"], [9, 1, 1, "", "Funct3"], [9, 1, 1, "", "Funct7"], [9, 1, 1, "", "ISA"], [9, 1, 1, "", "InstrType"], [9, 1, 1, "", "OpType"], [9, 1, 1, "", "Opcode"]], "coreblocks.params.isa.Extension": [[9, 2, 1, "", "A"], [9, 2, 1, "", "C"], [9, 2, 1, "", "D"], [9, 2, 1, "", "E"], [9, 2, 1, "", "F"], [9, 2, 1, "", "I"], [9, 2, 1, "", "M"], [9, 2, 1, "", "ZICSR"], [9, 2, 1, "", "ZIFENCEI"]], "coreblocks.params.isa.FenceFm": [[9, 2, 1, "", "NONE"], [9, 2, 1, "", "TSO"]], "coreblocks.params.isa.FenceTarget": [[9, 2, 1, "", "DEV_I"], [9, 2, 1, "", "DEV_O"], [9, 2, 1, "", "MEM_R"], [9, 2, 1, "", "MEM_W"]], "coreblocks.params.isa.Funct12": [[9, 2, 1, "", "EBREAK"], [9, 2, 1, "", "ECALL"], [9, 2, 1, "", "MRET"], [9, 2, 1, "", "WFI"]], "coreblocks.params.isa.Funct3": [[9, 2, 1, "", "ADD"], [9, 2, 1, "", "AND"], [9, 2, 1, "", "B"], [9, 2, 1, "", "BEQ"], [9, 2, 1, "", "BGE"], [9, 2, 1, "", "BGEU"], [9, 2, 1, "", "BLT"], [9, 2, 1, "", "BLTU"], [9, 2, 1, "", "BNE"], [9, 2, 1, "", "BU"], [9, 2, 1, "", "CSRRC"], [9, 2, 1, "", "CSRRCI"], [9, 2, 1, "", "CSRRS"], [9, 2, 1, "", "CSRRSI"], [9, 2, 1, "", "CSRRW"], [9, 2, 1, "", "CSRRWI"], [9, 2, 1, "", "FENCE"], [9, 2, 1, "", "FENCEI"], [9, 2, 1, "", "H"], [9, 2, 1, "", "HU"], [9, 2, 1, "", "JALR"], [9, 2, 1, "", "OR"], [9, 2, 1, "", "PRIV"], [9, 2, 1, "", "SLL"], [9, 2, 1, "", "SLT"], [9, 2, 1, "", "SLTU"], [9, 2, 1, "", "SR"], [9, 2, 1, "", "SUB"], [9, 2, 1, "", "W"], [9, 2, 1, "", "XOR"]], "coreblocks.params.isa.Funct7": [[9, 2, 1, "", "ADD"], [9, 2, 1, "", "AND"], [9, 2, 1, "", "OR"], [9, 2, 1, "", "SA"], [9, 2, 1, "", "SL"], [9, 2, 1, "", "SLT"], [9, 2, 1, "", "SUB"], [9, 2, 1, "", "XOR"]], "coreblocks.params.isa.InstrType": [[9, 2, 1, "", "B"], [9, 2, 1, "", "I"], [9, 2, 1, "", "J"], [9, 2, 1, "", "R"], [9, 2, 1, "", "S"], [9, 2, 1, "", "U"]], "coreblocks.params.isa.OpType": [[9, 2, 1, "", "ARITHMETIC"], [9, 2, 1, "", "AUIPC"], [9, 2, 1, "", "BRANCH"], [9, 2, 1, "", "COMPARE"], [9, 2, 1, "", "CSR"], [9, 2, 1, "", "EBREAK"], [9, 2, 1, "", "ECALL"], [9, 2, 1, "", "FENCE"], [9, 2, 1, "", "FENCEI"], [9, 2, 1, "", "JUMP"], [9, 2, 1, "", "LOAD"], [9, 2, 1, "", "LOGIC"], [9, 2, 1, "", "MRET"], [9, 2, 1, "", "SHIFT"], [9, 2, 1, "", "STORE"], [9, 2, 1, "", "UNKNOWN"], [9, 2, 1, "", "WFI"]], "coreblocks.params.isa.Opcode": [[9, 2, 1, "", "AUIPC"], [9, 2, 1, "", "BRANCH"], [9, 2, 1, "", "JAL"], [9, 2, 1, "", "JALR"], [9, 2, 1, "", "LOAD"], [9, 2, 1, "", "LUI"], [9, 2, 1, "", "MISC_MEM"], [9, 2, 1, "", "OP"], [9, 2, 1, "", "OP_IMM"], [9, 2, 1, "", "STORE"], [9, 2, 1, "", "SYSTEM"]], "coreblocks.params.layouts": [[9, 1, 1, "", "CommonLayouts"], [9, 1, 1, "", "DecodeLayouts"], [9, 1, 1, "", "FetchLayouts"], [9, 1, 1, "", "FuncUnitLayouts"], [9, 1, 1, "", "RATLayouts"], [9, 1, 1, "", "RFLayouts"], [9, 1, 1, "", "ROBLayouts"], [9, 1, 1, "", "RSLayouts"], [9, 1, 1, "", "SchedulerLayouts"]], "coreblocks.peripherals": [[10, 0, 0, "-", "wishbone"]], "coreblocks.peripherals.wishbone": [[10, 1, 1, "", "WishboneArbiter"], [10, 1, 1, "", "WishboneLayout"], [10, 1, 1, "", "WishboneMaster"], [10, 1, 1, "", "WishboneMemorySlave"], [10, 1, 1, "", "WishboneMuxer"], [10, 1, 1, "", "WishboneParameters"]], "coreblocks.peripherals.wishbone.WishboneMaster": [[10, 3, 1, "", "generate_layouts"]], "coreblocks.scheduler": [[11, 0, 0, "-", "scheduler"], [11, 0, 0, "-", "wakeup_select"]], "coreblocks.scheduler.scheduler": [[11, 1, 1, "", "Scheduler"]], "coreblocks.scheduler.wakeup_select": [[11, 1, 1, "", "WakeupSelect"]], "coreblocks.stages": [[12, 0, 0, "-", "backend"], [12, 0, 0, "-", "retirement"]], "coreblocks.stages.backend": [[12, 1, 1, "", "ResultAnnouncement"]], "coreblocks.stages.retirement": [[12, 1, 1, "", "Retirement"]], "coreblocks.structs_common": [[13, 0, 0, "-", "rat"], [13, 0, 0, "-", "rf"], [13, 0, 0, "-", "rob"], [13, 0, 0, "-", "rs"]], "coreblocks.structs_common.rat": [[13, 1, 1, "", "FRAT"], [13, 1, 1, "", "RRAT"]], "coreblocks.structs_common.rf": [[13, 1, 1, "", "RegisterFile"]], "coreblocks.structs_common.rob": [[13, 1, 1, "", "ReorderBuffer"]], "coreblocks.structs_common.rs": [[13, 1, 1, "", "RS"]], "coreblocks.transactions": [[14, 1, 1, "", "Method"], [14, 1, 1, "", "Transaction"], [14, 1, 1, "", "TransactionContext"], [14, 1, 1, "", "TransactionManager"], [14, 1, 1, "", "TransactionModule"], [14, 0, 0, "-", "core"], [14, 4, 1, "", "def_method"], [14, 0, 0, "-", "lib"]], "coreblocks.transactions.Method": [[14, 3, 1, "", "add_conflict"], [14, 3, 1, "", "body"], [14, 2, 1, "", "conflicts"], [14, 2, 1, "", "current"], [14, 3, 1, "", "debug_signals"], [14, 3, 1, "", "like"], [14, 2, 1, "", "method_uses"], [14, 3, 1, "", "use_method"]], "coreblocks.transactions.Transaction": [[14, 3, 1, "", "add_conflict"], [14, 3, 1, "", "body"], [14, 3, 1, "", "context"], [14, 2, 1, "", "current"], [14, 3, 1, "", "debug_signals"], [14, 3, 1, "", "get"], [14, 3, 1, "", "use_method"]], "coreblocks.transactions.TransactionContext": [[14, 3, 1, "", "get"], [14, 2, 1, "", "stack"]], "coreblocks.transactions.TransactionManager": [[14, 3, 1, "", "add_transaction"]], "coreblocks.transactions.TransactionModule": [[14, 3, 1, "", "transactionContext"]], "coreblocks.transactions.core": [[14, 1, 1, "", "Method"], [14, 1, 1, "", "Transaction"], [14, 1, 1, "", "TransactionContext"], [14, 1, 1, "", "TransactionManager"], [14, 1, 1, "", "TransactionModule"], [14, 4, 1, "", "def_method"], [14, 4, 1, "", "eager_deterministic_cc_scheduler"], [14, 4, 1, "", "trivial_roundrobin_cc_scheduler"]], "coreblocks.transactions.core.Method": [[14, 3, 1, "", "add_conflict"], [14, 3, 1, "", "body"], [14, 2, 1, "", "current"], [14, 3, 1, "", "debug_signals"], [14, 3, 1, "", "like"], [14, 3, 1, "", "use_method"]], "coreblocks.transactions.core.Transaction": [[14, 3, 1, "", "add_conflict"], [14, 3, 1, "", "body"], [14, 3, 1, "", "context"], [14, 2, 1, "", "current"], [14, 3, 1, "", "debug_signals"], [14, 3, 1, "", "get"], [14, 3, 1, "", "use_method"]], "coreblocks.transactions.core.TransactionContext": [[14, 3, 1, "", "get"], [14, 2, 1, "", "stack"]], "coreblocks.transactions.core.TransactionManager": [[14, 3, 1, "", "add_transaction"]], "coreblocks.transactions.core.TransactionModule": [[14, 3, 1, "", "transactionContext"]], "coreblocks.transactions.lib": [[14, 1, 1, "", "Adapter"], [14, 1, 1, "", "AdapterTrans"], [14, 1, 1, "", "CatTrans"], [14, 1, 1, "", "ClickIn"], [14, 1, 1, "", "ClickOut"], [14, 1, 1, "", "ConnectTrans"], [14, 1, 1, "", "FIFO"], [14, 1, 1, "", "ManyToOneConnectTrans"]], "coreblocks.utils": [[15, 0, 0, "-", "utils"]], "coreblocks.utils.utils": [[15, 1, 1, "", "AssignType"], [15, 4, 1, "", "OneHotSwitch"], [15, 4, 1, "", "OneHotSwitchDynamic"], [15, 4, 1, "", "assign"]], "coreblocks.utils.utils.AssignType": [[15, 2, 1, "", "ALL"], [15, 2, 1, "", "COMMON"], [15, 2, 1, "", "RHS"]]}, "objtypes": {"0": "py:module", "1": "py:class", "2": "py:attribute", "3": "py:method", "4": "py:function"}, "objnames": {"0": ["py", "module", "Python module"], "1": ["py", "class", "Python class"], "2": ["py", "attribute", "Python attribute"], "3": ["py", "method", "Python method"], "4": ["py", "function", "Python function"]}, "titleterms": {"list": 0, "assumpt": 0, "made": 0, "dure": 0, "develop": [0, 1], "environ": 1, "introduct": [2, 4], "document": [2, 4], "problem": 3, "checklist": 3, "coreblock": [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17], "transact": [4, 14], "framework": 4, "basic": 4, "usag": 4, "implement": [4, 19], "method": [4, 19, 20], "The": 4, "librari": 4, "api": 5, "packag": [6, 7, 8, 9, 10, 11, 12, 13, 14, 15], "subpackag": 6, "submodul": [6, 7, 8, 9, 10, 11, 12, 13, 14, 15], "core": [6, 14], "modul": [6, 7, 8, 9, 10, 11, 12, 13, 14, 15], "content": [6, 7, 8, 9, 10, 11, 12, 13, 14, 15], "frontend": 7, "decod": 7, "fetch": 7, "fu": 8, "alu": 8, "param": 9, "genparam": 9, "isa": 9, "layout": 9, "peripher": 10, "wishbon": 10, "schedul": [11, 18], "wakeup_select": 11, "stage": 12, "backend": 12, "retir": 12, "structs_common": 13, "rat": 13, "rf": 13, "rob": 13, "r": 13, "lib": 14, "util": 15, "overview": [18, 20], "descript": 18, "schema": 18, "structur": 18, "more": 18, "detail": 18, "each": 18, "block": 18, "proposit": 19, "reserv": [19, 20], "station": [19, 20], "intern": 19, "data": 19, "actual": 19, "us": [19, 20], "slot": [19, 20], "tabl": 19, "compar": [19, 20], "substitut": [19, 20], "read": [19, 20], "row": [19, 20], "clean": [19, 20], "get": [19, 20], "free": 19, "mark": [19, 20], "extern": [19, 20], "interfac": [19, 20], "all": [19, 20], "reset": 20, "initi": 20, "state": 20, "insert": 20, "new": 20, "instruct": 20, "readi": 20, "vector": 20, "signal": 20}, "envversion": {"sphinx.domains.c": 2, "sphinx.domains.changeset": 1, "sphinx.domains.citation": 1, "sphinx.domains.cpp": 6, "sphinx.domains.index": 1, "sphinx.domains.javascript": 2, "sphinx.domains.math": 2, "sphinx.domains.python": 3, "sphinx.domains.rst": 2, "sphinx.domains.std": 2, "sphinx.ext.todo": 2, "sphinx": 56}})