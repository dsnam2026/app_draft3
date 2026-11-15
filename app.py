"""Mailroom English Plus – 영어 단어 학습 앱 (Streamlit, 통합판)

두 앱의 기능을 하나로 합쳤습니다.
  · 수준 진단 → 추천 수준 안내 (초등 / 중·고등 / 확장)
  · 🃏 뒤집는 플래시카드 (뜻·품사·예문·발음, ⭐저장 / ✅외움)
  · 📝 퀴즈 3종: 영→한, 한→영, 철자 쓰기 (오답 시 힌트 + 재도전 → 정답 보기)
  · 📋 단어 목록 + 검색
  · 📖 읽기: 같은 이야기를 3가지 어휘 수준으로 읽기 / 문장별 비교 / 빈칸 채우기
  · ⭐ 내 단어: 저장 / 틀린 / 외운 단어 관리
  · 로그인(SQLite 저장) 또는 게스트 모드, 미국/영국 발음·속도 설정
  · (선택) ANTHROPIC_API_KEY 가 있으면 예문을 AI가 만들어 DB에 저장

준비
  - 이 파일(app.py)과 Voca_3000.csv 를 같은 폴더(깃허브 저장소 루트)에 두세요.
  - requirements.txt:  streamlit  /  pandas
실행:  streamlit run app.py
"""
import hashlib
import hmac
import html
import json
import os
import random
import re
import secrets
import sqlite3
import tempfile
import time
import urllib.request
from pathlib import Path

import pandas as pd
import streamlit as st
import streamlit.components.v1 as components

st.set_page_config(page_title="Mailroom English Plus", page_icon="✉️", layout="centered")

DATA_FILE = Path(__file__).parent / "Voca_3000.csv"

# 화면 이름 -> CSV의 Level 값
LEVELS = {"초등": "Elementary", "중·고등": "MidHigh", "확장": "Extended"}
LEVEL_NAMES = list(LEVELS)

DIAG_PER_LEVEL = 5
PASS_SCORE = 4
DONT_KNOW = "잘 모르겠어요"
SIZES = [10, 20, 30, 50]
GUEST = "__guest__"

EXTRA_EXAMPLES = {}  # 예: {"abandon": ["They had to abandon the car in the snow."]}
POS_FIX = {}         # 예: {"left": "adj"}

POS_NAMES = {"n": "명사", "v": "동사", "adj": "형용사", "adv": "부사", "prep": "전치사", "conj": "접속사",
             "pron": "대명사", "det": "한정사", "modal": "조동사", "num": "수사", "interj": "감탄사"}
POS_ABBR = {"n": "n.", "v": "v.", "adj": "adj.", "adv": "adv.", "prep": "prep.", "conj": "conj.",
            "pron": "pron.", "det": "det.", "modal": "modal", "num": "num.", "interj": "interj."}

# ───────────────────────── 품사 추정 ─────────────────────────
_CLOSED = {}


def _reg(pos, words):
    for w in words.split():
        _CLOSED[w] = pos


_reg("det", "a an the each every few many much several such this that these those some any all both another "
            "other either neither my your his her its our their enough")
_reg("pron", "i me you he him she it we us they them myself yourself himself herself itself ourselves themselves "
             "who whom whose what which something anything nothing everything someone anyone everyone nobody "
             "somebody anybody everybody none yours ours theirs")
_reg("num", "zero one two three four five six seven eight nine ten eleven twelve thirteen fourteen fifteen sixteen "
            "seventeen eighteen nineteen twenty thirty forty fifty sixty seventy eighty ninety hundred thousand "
            "million billion first third fourth fifth")
_reg("conj", "and or but because if though although unless whereas whether so than nor while")
_reg("prep", "about above across after against along among around as at before behind below beneath beside besides "
             "between beyond by despite during except for from in into of on onto over per since through "
             "throughout till to toward towards under until upon via with within without versus underneath")
_reg("modal", "can could may might must shall should would ought")
_reg("adv", "not never always often sometimes usually seldom already ago ahead abroad aside altogether away here "
            "there now then soon today tomorrow yesterday tonight once twice forever forth forward indeed down up "
            "out off maybe perhaps however therefore thus hence nevertheless nonetheless otherwise meanwhile "
            "likewise instead nowhere anywhere everywhere somewhere overnight apart alongside well later lately "
            "recently together almost also still just only even ever very too quite rather really again how when "
            "where why whenever wherever else frankly")
_reg("interj", "hello hi bye goodbye wow oh hey oops thanks no yes")
_reg("n", "adult agent alien attention brute butcher cause caution celebrity consent democracy factor favor fortune "
          "giant heir host index justice lecture luck master merchant minimum murder poet silver soldier sea")
_reg("adj", "far bad busy asleep blind correct dry early fast fat full glad gorgeous handsome ill lazy mad "
            "outstanding polite pretty quick rapid rare rough round sad sick slow sore steep swift tall tough "
            "tremendous ugly white")
_ADJ_END = ("의", "인", "한", "은", "는", "운", "된", "런")


def guess_pos(w, k):
    lw = w.lower()
    if lw in POS_FIX:
        return POS_FIX[lw]
    if lw in _CLOSED:
        return _CLOSED[lw]
    if k.endswith("다"):
        return "v"
    if k.endswith(_ADJ_END):
        return "adj"
    if lw.endswith("ly") and k.endswith(("히", "게", "이", "로")):
        return "adv"
    return "n"


# ───────────────────────── 읽기 지문 ─────────────────────────
# 표기법: [[단어]] = 그 수준의 단어, [[변형된 형태|기본 단어]]
STORY_TITLE = "✈️ 여행 이야기: 낯선 도시에서의 하루"
STORY_SUMMARY_KO = (
    "지난여름 친구와 큰 도시로 여행을 떠났다. 기차를 타고 가서 숙소에 짐을 풀고, 식당에서 맛있고 "
    "저렴한 저녁을 먹었다. 다음 날 오래된 다리를 보러 가려고 길에서 만난 여성에게 길을 물었고, "
    "그분이 친절하게 알려 주었다. 다리에서 사진을 많이 찍은 뒤 시장에서 어머니께 드릴 선물을 "
    "샀다. 짧은 여행이었지만 오래 기억할 것이다."
)
BEAT_LABELS = ["① 출발", "② 숙소", "③ 저녁 식사", "④ 길 묻기", "⑤ 다리에서", "⑥ 시장과 선물", "⑦ 마무리"]

PASSAGES = {
    "초등": {
        "note": "초등 어휘로 쓴 지문이에요.",
        "beats": [
            "Last summer, I took a [[trip]] to a big city with my friend. We went there by [[train]].",
            "First, we found our [[room]] and put our bags on the bed.",
            "We wanted to eat dinner, so we went to a [[restaurant]]. The food was [[delicious]], "
            "and it was [[cheap]].",
            "The next morning, we wanted to visit an old [[bridge]] by the river. We did not know the way, "
            "so we asked a woman on the [[street]]. She smiled and said, “Walk along this road, and turn "
            "left at the [[corner]].”",
            "We found the bridge and took many pictures.",
            "After that, we went to a [[market]]. I bought a present for my mother and paid [[cash]].",
            "It was a short trip, but I will always [[remember]] it.",
        ],
        "blanks": ["restaurant", "delicious", "bridge", "corner", "market", "cash"],
    },
    "중·고등": {
        "note": "초등 어휘에 중·고등 어휘를 더해 쓴 지문이에요.",
        "beats": [
            "Last summer, I went on a [[journey]] to a [[foreign]] city with my friend. We took a train there.",
            "When we [[reached|reach]] the [[hotel]], we put our bags in the room we had [[reserved|reserve]].",
            "In the evening, we wanted a good [[meal]], so we went to a restaurant. We looked at the [[menu]] "
            "and [[ordered|order]] a [[local]] [[dish]]. It tasted delicious, and the [[price]] was low.",
            "The next morning, we wanted to see an old bridge by the river, but we did not know the way. "
            "A [[polite]] woman on the street helped us. She smiled and said, “Go [[straight]], and turn "
            "left at the corner.”",
            "At the bridge, there was a big [[crowd]], but we still took many [[photos|photo]].",
            "After that, we went to a market. I bought a [[gift]] for my mother and paid in cash.",
            "It was a short trip, but I will always remember it.",
        ],
        "blanks": ["hotel", "menu", "local", "polite", "straight", "gift"],
        "gloss": {"order": "주문하다", "dish": "요리", "straight": "곧장"},
    },
    "확장": {
        "note": "확장 어휘까지 사용해 쓴 지문이에요.",
        "beats": [
            "Last summer, I traveled [[abroad]] with my friend to a [[vast]] city. Our train "
            "[[departed|depart]] from the [[platform]] at dawn.",
            "By evening, we reached a small [[inn]] that [[accommodated|accommodate]] us for the night. "
            "The room was small and far from [[luxury]].",
            "We were [[eager]] to eat, so we found a restaurant and ordered an [[exotic]] dish with a rich "
            "[[flavor]]. It was delicious, and the price was a real [[bargain]].",
            "The next morning, we wanted to see an [[ancient]] bridge by the river, but we could not find it. "
            "We [[inquired|inquire]] of a woman on the street, and we were [[grateful]] for her help. She "
            "smiled and said, “Continue straight, then turn left at the corner.”",
            "At the bridge, we took many photographs of the [[landscape]].",
            "Then, we [[wandered|wander]] through a market, where I bought a gift for my mother. I paid in "
            "local [[currency]] and kept the [[receipt]].",
            "It was a brief trip, but I will always remember it.",
        ],
        "blanks": ["inn", "exotic", "bargain", "ancient", "inquire", "currency"],
        "gloss": {"bargain": "싸게 산 물건", "luxury": "호화로움", "accommodate": "묵게 해 주다"},
    },
}

MARK_RE = re.compile(r"\[\[([^\]|]+)(?:\|([^\]]+))?\]\]")
MARK_STYLE = "background:rgba(255,193,7,.35);border-radius:4px;padding:0 3px;font-weight:600;"
BLANK_STYLE = "border-bottom:2px solid currentColor;padding:0 10px;font-weight:700;"
COMPARE = "🔍 문장별 비교"
ACT_READ, ACT_CLOZE = "📖 읽기", "✏️ 빈칸 채우기"
NO_PICK = "선택"


def parse_marks(text):
    parts, last = [], 0
    for m in MARK_RE.finditer(text):
        if m.start() > last:
            parts.append(("text", text[last:m.start()]))
        parts.append(("word", m.group(1), m.group(2) or m.group(1)))
        last = m.end()
    if last < len(text):
        parts.append(("text", text[last:]))
    return parts


def strip_marks(text):
    return MARK_RE.sub(lambda m: m.group(1), text)


# ───────────────────────── 데이터 ─────────────────────────
@st.cache_data
def load_words():
    df = pd.read_csv(DATA_FILE, encoding="utf-8-sig", keep_default_na=False)
    df = df.rename(columns={"Korean meaning (뜻)": "Meaning"})
    for col in ["Word", "Meaning", "Variation"]:
        df[col] = df[col].astype(str).str.strip()
    df["Variation"] = df["Variation"].replace({"NA": ""})
    code_to_name = {v: k for k, v in LEVELS.items()}
    words = {}
    for no, w, lv, k, var in zip(df["No."], df["Word"], df["Level"], df["Meaning"], df["Variation"]):
        if not w:
            continue
        if w in words:  # 같은 철자가 여러 번 나오면 뜻을 합침
            if k and k not in words[w]["k"]:
                words[w]["k"] += "; " + k
            continue
        words[w] = dict(w=w, no=int(no), level=code_to_name.get(lv, lv), k=k, var=var, pos=guess_pos(w, k))
    return words


@st.cache_data
def passage_examples():
    """읽기 지문의 문장에서 단어별 예문을 뽑음 (원본 단어/변형 표기 모두)"""
    out = {}
    for name in LEVEL_NAMES:
        for beat in PASSAGES[name]["beats"]:
            for sent in re.split(r"(?<=[.!?”])\s+", beat):
                plain = strip_marks(sent).strip()
                for part in parse_marks(sent):
                    if part[0] == "word":
                        lst = out.setdefault(part[2].lower(), [])
                        if plain not in lst:
                            lst.append(plain)
    return out


if not DATA_FILE.exists():
    st.error(f"{DATA_FILE.name} 파일을 app.py 와 같은 폴더에 넣어 주세요.")
    st.stop()

W = load_words()
ALL = list(W)
LEVEL_WORDS = {lv: [w for w in ALL if W[w]["level"] == lv] for lv in LEVEL_NAMES}


def pos_label(w):
    return f"{POS_NAMES[W[w]['pos']]} ({POS_ABBR[W[w]['pos']]})"


# ───────────────────────── 저장소 (SQLite / 게스트) ─────────────────────────
def _db_path():
    p = os.environ.get("VOCA_DB")
    if p:
        return p
    d = Path(__file__).parent
    if not os.access(d, os.W_OK):
        d = Path(tempfile.gettempdir())
    return str(d / "voca.db")


DB_PATH = _db_path()


def _c():
    con = sqlite3.connect(DB_PATH, timeout=10)
    con.row_factory = sqlite3.Row
    return con


def db_init():
    with _c() as c:
        c.executescript("""
        CREATE TABLE IF NOT EXISTS users(username TEXT PRIMARY KEY, salt TEXT, pw TEXT, created REAL);
        CREATE TABLE IF NOT EXISTS marks(username TEXT, word TEXT, kind TEXT, n INT DEFAULT 1,
            PRIMARY KEY(username, word, kind));
        CREATE TABLE IF NOT EXISTS examples(word TEXT PRIMARY KEY, data TEXT);
        """)


def _hash(pw, salt):
    return hashlib.pbkdf2_hmac("sha256", pw.encode(), bytes.fromhex(salt), 120_000).hex()


def db_register(user, pw):
    user = user.strip()
    if not (2 <= len(user) <= 16) or user == GUEST:
        return "ID는 2~16자로 입력해 주세요."
    if len(pw) < 4:
        return "비밀번호는 4자 이상이어야 해요."
    salt = secrets.token_hex(16)
    try:
        with _c() as c:
            c.execute("INSERT INTO users VALUES(?,?,?,?)", (user, salt, _hash(pw, salt), time.time()))
    except sqlite3.IntegrityError:
        return "이미 있는 ID예요."
    return None


def db_verify(user, pw):
    with _c() as c:
        r = c.execute("SELECT salt, pw FROM users WHERE username=?", (user.strip(),)).fetchone()
    return bool(r) and hmac.compare_digest(r["pw"], _hash(pw, r["salt"]))


ss = st.session_state
for _k, _v in dict(user=None, page="home", fc=None, qz=None, accent="US", rate=1.0, qkind="en2ko",
                   sel=dict(src="초등", size=20, setno=0, shuffle=False), gm={},
                   diag_state="intro", diag_questions=[], diag_result=None).items():
    ss.setdefault(_k, _v)
U = ss.user


def marks(kind):
    """{word: n}  (kind: star / known / missed)"""
    if U == GUEST:
        return dict(ss.gm.get(kind, {}))
    with _c() as c:
        return {r["word"]: r["n"] for r in c.execute(
            "SELECT word, n FROM marks WHERE username=? AND kind=?", (U, kind))}


def mark(word, kind):
    if U == GUEST:
        d = ss.gm.setdefault(kind, {})
        d[word] = d.get(word, 0) + 1
        return
    with _c() as c:
        c.execute("""INSERT INTO marks(username,word,kind,n) VALUES(?,?,?,1)
                     ON CONFLICT(username,word,kind) DO UPDATE SET n=n+1""", (U, word, kind))


def unmark(word, kind):
    if U == GUEST:
        ss.gm.get(kind, {}).pop(word, None)
        return
    with _c() as c:
        c.execute("DELETE FROM marks WHERE username=? AND word=? AND kind=?", (U, word, kind))


def ex_get(words):
    if not words:
        return {}
    with _c() as c:
        q = ",".join("?" * len(words))
        return {r["word"]: json.loads(r["data"]) for r in c.execute(
            f"SELECT word, data FROM examples WHERE word IN ({q})", list(words))}


def ex_put(word, sentences):
    with _c() as c:
        c.execute("INSERT OR REPLACE INTO examples VALUES(?,?)", (word, json.dumps(sentences, ensure_ascii=False)))


db_init()


# ───────────────────────── 예문 (지문 + 직접 입력 + 선택적 AI) ─────────────────────────
def _secret(name):
    v = os.environ.get(name)
    if v:
        return v
    try:
        return st.secrets.get(name)
    except Exception:
        return None


def _gen_examples(words):
    key = _secret("ANTHROPIC_API_KEY")
    if not key or not words:
        return {}
    lines = "\n".join(f"- {w} ({W[w]['k']})" for w in words)
    prompt = ("For each English word below, write 2 short, natural example sentences (8-14 words each) for a Korean "
              "middle-school learner. Use the word in the meaning given in parentheses. Reply with JSON only, no "
              'markdown: {"word": ["sentence 1", "sentence 2"], ...}\n\nWords:\n' + lines)
    body = json.dumps({"model": _secret("ANTHROPIC_MODEL") or "claude-haiku-5-5", "max_tokens": 3000,
                       "messages": [{"role": "user", "content": prompt}]}).encode()
    req = urllib.request.Request("https://api.anthropic.com/v1/messages", data=body, headers={
        "content-type": "application/json", "x-api-key": key, "anthropic-version": "2023-06-01"})
    with urllib.request.urlopen(req, timeout=60) as r:
        data = json.load(r)
    text = "".join(b.get("text", "") for b in data.get("content", []))
    obj = json.loads(text[text.index("{"): text.rindex("}") + 1])
    out = {}
    for w in words:
        v = obj.get(w)
        if isinstance(v, list) and v and all(isinstance(s, str) for s in v):
            out[w] = [s.strip() for s in v[:2]]
    return out


def local_examples(w):
    lw = w.lower()
    if lw in EXTRA_EXAMPLES:
        v = EXTRA_EXAMPLES[lw]
        return [v] if isinstance(v, str) else list(v)
    return passage_examples().get(lw, [])


def ensure_examples(words):
    """예문이 없는 단어는 (API 키가 있을 때만) 25개씩 AI로 생성해 DB에 저장"""
    if not _secret("ANTHROPIC_API_KEY"):
        return
    tried = ss.setdefault("ex_tried", set())
    cached = ex_get(words)
    missing = [w for w in words if not local_examples(w) and w not in cached and w not in tried]
    if not missing:
        return
    with st.spinner("예문을 준비하고 있어요…"):
        for i in range(0, len(missing), 25):
            chunk = missing[i:i + 25]
            tried.update(chunk)
            try:
                for w, s in _gen_examples(chunk).items():
                    ex_put(w, s)
            except Exception:
                pass


def examples_for(w):
    return local_examples(w) or ex_get([w]).get(w, [])


# ───────────────────────── 음성 / 카드 UI ─────────────────────────
def apply_style():
    st.markdown("""<style>
.bigw{font-size:2.6rem;font-weight:700;line-height:1.2;margin:.3rem 0;text-align:center}
.bigk{font-size:1.9rem;font-weight:700;line-height:1.3;margin:.3rem 0;text-align:center}
.tag{display:inline-block;background:#e3ebff;color:#2d5fb4;border-radius:10px;padding:0 10px;font-size:.85rem}
.center{text-align:center}
</style>""", unsafe_allow_html=True)


def _tts_js():
    lang = "en-GB" if ss.accent == "GB" else "en-US"
    return ("const L=%s,R=%s;function say(t){try{speechSynthesis.cancel();const u=new SpeechSynthesisUtterance(t);"
            "u.lang=L;u.rate=R;const v=speechSynthesis.getVoices().find(v=>v.lang.replace('_','-')===L);"
            "if(v)u.voice=v;speechSynthesis.speak(u)}catch(e){}}" % (json.dumps(lang), float(ss.rate)))


def speak_bar(items, height=46):
    data = json.dumps(items, ensure_ascii=False).replace("</", "<\\/")
    components.html(
        "<style>body{margin:0;text-align:center}button{font-size:15px;padding:4px 14px;margin:2px 4px;"
        "border:1px solid #9aa;border-radius:8px;background:#f4f6fa;cursor:pointer}</style><div id=b></div>"
        f"<script>{_tts_js()}const I={data};I.forEach(([l,t])=>{{const b=document.createElement('button');"
        "b.textContent=l;b.onclick=()=>say(t);document.getElementById('b').appendChild(b)});</script>", height=height)


_CARD = """<style>
html,body{margin:0;background:transparent;font-family:-apple-system,'Segoe UI','Noto Sans KR','Malgun Gothic','Apple SD Gothic Neo',sans-serif}
.scene{perspective:1000px;height:310px;cursor:pointer;-webkit-tap-highlight-color:transparent}
.card{position:relative;width:100%;height:100%;transition:transform .45s;transform-style:preserve-3d}
.card.f{transform:rotateY(180deg)}
.face{position:absolute;inset:0;backface-visibility:hidden;-webkit-backface-visibility:hidden;border:1px solid #c5d0e6;
border-radius:18px;background:#fff;color:#16191f;display:flex;overflow:auto;box-sizing:border-box;padding:16px;text-align:center}
.back{transform:rotateY(180deg);background:#f4f7ff}
.in{margin:auto;width:100%}
.w{font-size:46px;font-weight:700;line-height:1.15;word-break:break-word}
.w2{font-size:20px;color:#5a6478;font-weight:600}
.pos{display:inline-block;background:#e3ebff;color:#2d5fb4;border-radius:10px;padding:1px 10px;font-size:13px;margin:6px 0}
.k{font-size:30px;font-weight:700;margin:4px 0 8px;word-break:keep-all}
.var{font-size:13px;color:#5a6478;margin-bottom:6px}
.ex{font-size:15px;color:#333;text-align:left;margin:6px auto;max-width:520px}
.none{font-size:13px;color:#99a2b5}
.tip{font-size:13px;color:#8892a6;margin-top:14px}
button{font-size:14px;border:1px solid #9aa7c4;border-radius:8px;background:#f4f6fa;cursor:pointer;padding:2px 8px;margin-left:6px}
</style>
<div class=scene id=s><div class=card id=c>
<div class="face front"><div class=in><div class=w id=fw></div><div><button id=fs>🔊</button></div>
<div class=tip>카드를 누르면 뜻이 보여요</div></div></div>
<div class="face back"><div class=in><div class=w2><span id=bw></span><button id=bs>🔊</button></div>
<div class=pos id=pos></div><div class=k id=k></div><div class=var id=var></div><div id=ex></div></div></div>
</div></div>
<script>
const D=@@DATA@@;const $=id=>document.getElementById(id);@@TTS@@
$('fw').textContent=D.w;$('bw').textContent=D.w;$('pos').textContent=D.pos;$('k').textContent=D.k;
if(D.var)$('var').textContent='관련 형태: '+D.var;
D.ex.forEach(t=>{const p=document.createElement('div');p.className='ex';p.textContent='• '+t;
const b=document.createElement('button');b.textContent='🔊';b.onclick=e=>{e.stopPropagation();say(t)};p.appendChild(b);$('ex').appendChild(p)});
if(!D.ex.length){const p=document.createElement('div');p.className='none';p.textContent='예문 없음';$('ex').appendChild(p)}
$('fs').onclick=e=>{e.stopPropagation();say(D.w)};$('bs').onclick=e=>{e.stopPropagation();say(D.w)};
$('s').onclick=()=>$('c').classList.toggle('f');
</script>"""


def show_card(w):
    d = W[w]
    data = json.dumps(dict(w=w, k=d["k"], var=d["var"], pos=pos_label(w), ex=examples_for(w)),
                      ensure_ascii=False).replace("</", "<\\/")
    components.html(_CARD.replace("@@DATA@@", data).replace("@@TTS@@", _tts_js()), height=325)


# ───────────────────────── 학습 범위(세트) 선택 ─────────────────────────
def source_words(src):
    if src in LEVELS:
        return LEVEL_WORDS[src]
    if src == "all":
        return ALL
    m = marks("star" if src == "star" else "missed")
    return [w for w in ALL if w in m]


def split_sets(words, size):
    return [words[i:i + size] for i in range(0, len(words), size)]


def current_set():
    sel = ss.sel
    sets = split_sets(source_words(sel["src"]), sel["size"])
    if not sets:
        return [], ""
    j = min(sel["setno"], len(sets) - 1)
    name = {"star": "⭐ 저장한 단어", "missed": "❌ 틀린 단어", "all": "전체"}.get(sel["src"], sel["src"])
    return sets[j], f"{name} · 세트 {j + 1}"


def render_picker():
    sel = ss.sel
    star, miss, known = marks("star"), marks("missed"), marks("known")
    names = {**{lv: f"{lv} ({len(LEVEL_WORDS[lv]):,})" for lv in LEVEL_NAMES}, "all": f"전체 ({len(ALL):,})",
             "star": f"⭐ 저장 ({len(star)})", "missed": f"❌ 틀린 단어 ({len(miss)})"}
    codes = list(names)
    if sel["src"] not in codes:
        sel["src"] = codes[0]
    sel["src"] = st.radio("공부할 단어", codes, index=codes.index(sel["src"]), format_func=names.get, horizontal=True)
    c1, c2 = st.columns([1, 3])
    sel["size"] = c1.selectbox("세트 크기", SIZES, index=SIZES.index(sel["size"]))
    sets = split_sets(source_words(sel["src"]), sel["size"])
    if not sets:
        st.info("아직 이 목록에 단어가 없어요. 다른 단어 묶음을 골라 보세요.")
        return
    sel["setno"] = min(sel["setno"], len(sets) - 1)

    def label(j):
        s = sets[j]
        return f"세트 {j + 1} · {s[0]} – {s[-1]} · ✓ {sum(w in known for w in s)}/{len(s)}"
    sel["setno"] = c2.selectbox("세트", list(range(len(sets))), index=sel["setno"], format_func=label)
    sel["shuffle"] = st.toggle("순서 섞기", value=sel["shuffle"])


def ordered(words):
    return random.sample(words, len(words)) if ss.sel["shuffle"] else list(words)


def go(page):
    ss.nav = page


# ───────────────────────── 🏠 시작 / 수준 진단 ─────────────────────────
def make_options(word, level=None):
    """정답 단어 + 같은 수준의 오답 3개 (뜻이 같거나 철자가 비슷한 단어는 제외)"""
    import difflib
    t = W[word]
    pool = LEVEL_WORDS[level or t["level"]]
    ds, seen = [], {t["k"]}
    for x in random.sample(pool, min(len(pool), 150)):
        if x == word or W[x]["k"] in seen:
            continue
        if difflib.SequenceMatcher(None, x.lower(), word.lower()).ratio() >= 0.8:
            continue
        ds.append(x)
        seen.add(W[x]["k"])
        if len(ds) == 3:
            break
    opts = [word] + ds
    random.shuffle(opts)
    return opts


def start_diag():
    qs = []
    for name in LEVEL_NAMES:
        for w in random.sample(LEVEL_WORDS[name], min(DIAG_PER_LEVEL, len(LEVEL_WORDS[name]))):
            qs.append(dict(level=name, word=w, answer=W[w]["k"],
                           options=[W[o]["k"] for o in make_options(w)] + [DONT_KNOW]))
    ss.diag_questions = qs
    ss.diag_state = "running"


def recommend(scores):
    rec = LEVEL_NAMES[0]
    for i, name in enumerate(LEVEL_NAMES[:-1]):
        if scores[name] >= PASS_SCORE:
            rec = LEVEL_NAMES[i + 1]
        else:
            break
    return rec


def study_level(name):
    ss.sel.update(src=name, setno=0)
    ss.fc = None
    go("cards")


def page_home():
    if ss.diag_state == "running":
        qs = ss.diag_questions
        st.subheader("🧭 내 수준 확인하기")
        st.write(f"아는 만큼만 골라 보세요. 모르면 '{DONT_KNOW}'를 골라도 괜찮아요. (총 {len(qs)}문항)")
        with st.form("diag_form"):
            for i, q in enumerate(qs):
                st.radio(f"**{i + 1}. {q['word']}**", q["options"], index=None, key=f"diag_q_{i}")
            submitted = st.form_submit_button("결과 보기", type="primary")
        if submitted:
            scores = {n: 0 for n in LEVEL_NAMES}
            for i, q in enumerate(qs):
                if ss.get(f"diag_q_{i}") == q["answer"]:
                    scores[q["level"]] += 1
            ss.diag_result = dict(scores=scores, recommended=recommend(scores))
            ss.diag_state = "done"
            st.rerun()
        if st.button("← 돌아가기"):
            ss.diag_state = "intro"
            st.rerun()
        return
    if ss.diag_state == "done" and ss.diag_result:
        res = ss.diag_result
        st.subheader("🧭 진단 결과")
        cols = st.columns(len(LEVEL_NAMES))
        for col, n in zip(cols, LEVEL_NAMES):
            col.metric(n, f"{res['scores'][n]} / {DIAG_PER_LEVEL}")
        st.success(f"**{res['recommended']}** 단어부터 시작하면 좋아요! 추천일 뿐이라서 다른 수준도 자유롭게 고를 수 있어요.")
        st.button(f"👉 {res['recommended']} 학습 시작", type="primary", on_click=study_level, args=(res["recommended"],))
        st.caption("다른 수준으로 바로 가기")
        cols = st.columns(len(LEVEL_NAMES))
        for col, n in zip(cols, LEVEL_NAMES):
            col.button(f"{n} ({len(LEVEL_WORDS[n]):,}개)", key=f"res_{n}", on_click=study_level, args=(n,))
        st.button("🔄 진단 다시 하기", on_click=start_diag)
        return
    st.write("교육과정 기본 어휘를 **내가 고른 순서대로** 공부해요. "
             "먼저 간단한 진단으로 내 수준을 확인하거나, 바로 시작할 수 있어요.")
    c1, c2 = st.columns(2)
    c1.button("🧭 내 수준 확인하기 (약 3분)", type="primary", on_click=start_diag, use_container_width=True)
    c2.button("바로 학습 시작", on_click=study_level, args=(LEVEL_NAMES[0],), use_container_width=True)
    known = marks("known")
    st.caption("수준별 단어 수 · 외운 단어")
    cols = st.columns(len(LEVEL_NAMES))
    for col, n in zip(cols, LEVEL_NAMES):
        col.metric(n, f"{len(LEVEL_WORDS[n]):,}개", f"✓ {sum(w in known for w in LEVEL_WORDS[n])}")


# ───────────────────────── 🃏 플래시카드 ─────────────────────────
def start_cards():
    words, label = current_set()
    if words:
        ensure_examples(words)
        ss.fc = dict(order=ordered(words), i=0, label=label)


def page_cards():
    fc = ss.fc
    if not fc:
        st.write("카드를 눌러 뜻·품사·예문을 확인하세요. 이전 카드로도 자유롭게 돌아갈 수 있어요.")
        render_picker()
        words, _ = current_set()
        if st.button("🃏 플래시카드 시작", type="primary", disabled=not words, use_container_width=True):
            start_cards()
            st.rerun()
        return
    order, i = fc["order"], fc["i"]
    n, w = len(order), order[fc["i"]]
    a, b = st.columns([4, 1])
    a.progress((i + 1) / n, text=f"{i + 1} / {n} · {fc['label']}")
    if b.button("✖ 나가기", key="fc_exit", use_container_width=True):
        ss.fc = None
        st.rerun()
    star, known = marks("star"), marks("known")
    show_card(w)
    c1, c2, c3, c4 = st.columns([2, 1.3, 1.5, 2])
    if c1.button("◀ 이전", key="fc_prev", disabled=i == 0, use_container_width=True):
        fc["i"] -= 1
        st.rerun()
    if c2.button("⭐ 저장됨" if w in star else "☆ 저장", key="fc_star", use_container_width=True):
        (unmark if w in star else mark)(w, "star")
        st.rerun()
    if c3.button("✅ 외웠어요" if w in known else "⬜ 외웠어요", key="fc_known", use_container_width=True):
        (unmark if w in known else mark)(w, "known")
        st.rerun()
    if c4.button("다음 ▶", key="fc_next", type="primary", disabled=i == n - 1, use_container_width=True):
        fc["i"] += 1
        st.rerun()
    if i == n - 1:
        st.success("마지막 카드예요.")
        x, y = st.columns(2)
        if x.button("↺ 처음부터 다시", key="fc_again", use_container_width=True):
            fc["i"] = 0
            st.rerun()
        if y.button("📝 이 세트 퀴즈 풀기", key="fc_to_quiz", use_container_width=True):
            ss.fc = None
            start_quiz()
            go("quiz")
            st.rerun()


# ───────────────────────── 📝 퀴즈 (영→한 / 한→영 / 철자) ─────────────────────────
KIND_LABEL = {"en2ko": "🔤 영어 → 뜻 고르기", "ko2en": "🔁 뜻 → 영어 고르기", "spell": "✍️ 철자 쓰기"}


def new_question(qz):
    w = qz["order"][qz["i"]]
    q = dict(w=w, wrong=[], status=None)
    if qz["kind"] != "spell":
        q["opts"] = make_options(w)
    qz["q"] = q


def start_quiz():
    words, label = current_set()
    if not words:
        return
    ensure_examples(words)
    qz = dict(order=ordered(words), i=0, label=label, kind=ss.qkind, res={}, done=False)
    new_question(qz)
    ss.qz = qz


def hint_text(w, kind):
    d = W[w]
    parts = [f"품사: **{pos_label(w)}**"]
    if kind == "en2ko":
        parts.append(f"뜻은 **'{d['k'][0]}'** (으)로 시작하고 총 **{len(d['k'])}글자**예요.")
    else:
        parts.append(f"첫 글자는 **{w[0]}**, 총 **{len(w)}글자**예요.")
    if kind == "spell":
        parts.append("철자 힌트: `" + " ".join(w[0] + "".join("_" if ch.isalpha() else ch for ch in w[1:])) + "`")
    if len(w) >= 3:
        for s in examples_for(w)[:1]:
            masked, cnt = re.subn(rf"\b{re.escape(w)}\w*", "＿＿＿", s, flags=re.I)
            if cnt:
                parts.append(f"예문: *{masked}*")
    return "  \n".join(parts)


def finish_question(qz, status):
    q = qz["q"]
    q["status"] = status
    qz["res"][q["w"]] = status
    if status == "first":
        mark(q["w"], "known")
        unmark(q["w"], "missed")


def answer_question(qz, ok, choice=None):
    q = qz["q"]
    if ok:
        k = len(q["wrong"])
        finish_question(qz, "first" if k == 0 else "second" if k == 1 else "later")
    else:
        q["wrong"].append(choice)
        if len(q["wrong"]) == 1:
            mark(q["w"], "missed")


def page_quiz():
    qz = ss.qz
    if not qz:
        return quiz_ready()
    if qz["done"]:
        return quiz_summary(qz)
    quiz_run(qz)


def quiz_ready():
    st.write("원하는 세트를 골라 풀어 보세요. 틀리면 힌트와 다시 도전할 기회가 있어요.")
    render_picker()
    kinds = list(KIND_LABEL)
    ss.qkind = st.radio("문제 유형", kinds, index=kinds.index(ss.qkind), horizontal=True, format_func=KIND_LABEL.get)
    words, _ = current_set()
    if st.button("📝 퀴즈 시작", type="primary", disabled=not words, use_container_width=True):
        start_quiz()
        st.rerun()


def quiz_run(qz):
    n, i, q, kind = len(qz["order"]), qz["i"], qz["q"], qz["kind"]
    w = q["w"]
    a, b = st.columns([4, 1])
    a.progress(i / n, text=f"{i + 1} / {n} · {qz['label']}")
    if b.button("✖ 나가기", key="qz_exit", use_container_width=True):
        qz["done"] = True
        st.rerun()
    answered = q["status"] is not None
    with st.container(border=True):
        if kind == "en2ko":
            st.markdown(f"<div class='bigw'>{html.escape(w)}</div>", unsafe_allow_html=True)
            speak_bar([("🔊 듣기", w)])
        else:
            st.markdown(f"<div class='bigk'>{html.escape(W[w]['k'])}</div>"
                        f"<div class='center'><span class='tag'>{pos_label(w)}</span></div>", unsafe_allow_html=True)
        if kind == "spell":
            if not answered:
                with st.form(f"sp_{i}_{len(q['wrong'])}"):
                    typed = st.text_input("영어 철자를 입력하세요")
                    sub = st.form_submit_button("확인", type="primary")
                if sub and typed.strip():
                    answer_question(qz, typed.strip().lower() == w.lower(), typed.strip())
                    st.rerun()
        else:
            label = (lambda o: W[o]["k"]) if kind == "en2ko" else (lambda o: o)
            cols = st.columns(2)
            for j, o in enumerate(q["opts"]):
                if cols[j % 2].button(label(o), key=f"qo{i}_{j}", use_container_width=True,
                                      disabled=answered or o in q["wrong"]):
                    answer_question(qz, o == w, o)
                    st.rerun()
    nw = len(q["wrong"])
    if not answered:
        if nw >= 1:
            st.warning("아쉬워요! 힌트를 보고 다시 해 보세요.  \n" + hint_text(w, kind))
        if nw >= 2 and st.button("👀 정답 보기", key=f"rev{i}", use_container_width=True):
            finish_question(qz, "revealed")
            st.rerun()
        return
    if q["status"] == "revealed":
        st.info(f"정답: **{w}** — {W[w]['k']} ({pos_label(w)})")
    else:
        st.success("✅ 정답! 한 번에 맞혔어요." if q["status"] == "first" else "✅ 정답! (힌트를 보고 맞혔어요)")
    speak_bar([("🔊 발음", w)])
    for s in examples_for(w)[:1]:
        st.caption(f"• {s}")
    last = i == n - 1
    if st.button("결과 보기 ▶" if last else "다음 ▶", key=f"nx{i}", type="primary", use_container_width=True):
        if last:
            qz["done"] = True
        else:
            qz["i"] += 1
            new_question(qz)
        st.rerun()


def quiz_summary(qz):
    res, total = qz["res"], len(qz["order"])
    first = sum(v == "first" for v in res.values())
    hinted = sum(v in ("second", "later") for v in res.values())
    shown = sum(v == "revealed" for v in res.values())
    st.subheader("퀴즈 결과" if len(res) == total else f"퀴즈를 마쳤어요 ({len(res)}/{total}문제)")
    st.caption(f"{qz['label']} · {KIND_LABEL[qz['kind']]}")
    c = st.columns(3)
    c[0].metric("한 번에 정답", first)
    c[1].metric("힌트 후 정답", hinted)
    c[2].metric("정답 확인", shown)
    wrong = [w for w, v in res.items() if v != "first"]
    if wrong:
        st.write("다시 볼 단어 (❌ 틀린 단어에 저장됐어요)")
        st.dataframe([{"단어": w, "품사": pos_label(w), "뜻": W[w]["k"]} for w in wrong],
                     hide_index=True, use_container_width=True)
    x, y, z = st.columns(3)
    if x.button("↺ 같은 세트 다시", use_container_width=True):
        start_quiz()
        st.rerun()
    if y.button("🃏 카드로 복습", use_container_width=True):
        ss.qz = None
        start_cards()
        go("cards")
        st.rerun()
    if z.button("세트 다시 고르기", use_container_width=True):
        ss.qz = None
        st.rerun()


# ───────────────────────── 📋 단어 목록 ─────────────────────────
def page_list():
    c1, c2 = st.columns([2, 3])
    scope = c1.selectbox("범위", ["전체", *LEVEL_NAMES], key="w_list_scope")
    q = c2.text_input("🔍 검색 (영어 또는 한국어)", key="w_list_q").strip()
    words = ALL if scope == "전체" else LEVEL_WORDS[scope]
    rows = []
    for w in words:
        d = W[w]
        if q and q.lower() not in w.lower() and q not in d["k"] and q.lower() not in d["var"].lower():
            continue
        rows.append({"번호": d["no"], "단어": w, "수준": d["level"], "품사": pos_label(w),
                     "뜻": d["k"], "변형 표기": d["var"]})
    st.caption(f"{len(rows):,}개")
    st.dataframe(pd.DataFrame(rows), hide_index=True, height=460, use_container_width=True)


# ───────────────────────── 📖 읽기 ─────────────────────────
def render_parts(parts, show_marks=True, blank_numbers=None):
    out, used = [], set()
    for part in parts:
        if part[0] == "text":
            out.append(html.escape(part[1]))
            continue
        _, surface, base = part
        if blank_numbers and base in blank_numbers and base not in used:
            used.add(base)
            out.append(f"<span style='{BLANK_STYLE}'>({blank_numbers[base]}) ______</span>")
        elif show_marks:
            out.append(f"<span style='{MARK_STYLE}'>{html.escape(surface)}</span>")
        else:
            out.append(html.escape(surface))
    return "".join(out)


def show_html(body):
    st.markdown(f"<div style='line-height:2;font-size:1.05rem;'>{body}</div>", unsafe_allow_html=True)


def passage_parts(name):
    return parse_marks(" ".join(PASSAGES[name]["beats"]))


def keyword_table(name):
    gloss = PASSAGES[name].get("gloss", {})
    rows, seen = [], set()
    for part in passage_parts(name):
        if part[0] == "word" and part[2] not in seen:
            seen.add(part[2])
            base = part[2]
            meaning = gloss.get(base) or (W[base]["k"] if base in W else
                                          next((W[x]["k"] for x in ALL if base.lower() in
                                                [v.strip().lower() for v in W[x]["var"].split(",")]), ""))
            rows.append({"단어": base, "지문에 나온 모양": part[1], "뜻 (이 지문에서)": meaning})
    return pd.DataFrame(rows)


def cloze_order(name):
    order = []
    for part in passage_parts(name):
        if part[0] == "word" and part[2] in PASSAGES[name]["blanks"] and part[2] not in [b for b, _ in order]:
            order.append((part[2], part[1]))
    return order


def reset_cloze(name, count):
    ss[f"read_checked_{name}"] = False
    for i in range(count):
        ss[f"w_cloze_{name}_{i}"] = NO_PICK


def check_cloze(name):
    ss[f"read_checked_{name}"] = True


def reading_cloze(name, show_marks):
    order = cloze_order(name)
    numbers = {base: i + 1 for i, (base, _) in enumerate(order)}
    show_html(render_parts(passage_parts(name), show_marks, numbers))
    bank = [surface for _, surface in order]
    random.Random(name).shuffle(bank)
    st.markdown("**단어 상자:** " + " · ".join(f"`{w}`" for w in bank))
    checked_key = f"read_checked_{name}"
    ss.setdefault(checked_key, False)
    for i in range(len(order)):
        key = f"w_cloze_{name}_{i}"
        ss.setdefault(key, NO_PICK)
        st.selectbox(f"({i + 1})", [NO_PICK, *bank], key=key)
    b1, b2 = st.columns(2)
    b1.button("✅ 정답 확인", key=f"read_check_{name}", type="primary", on_click=check_cloze, args=(name,))
    b2.button("🔄 다시 풀기", key=f"read_reset_{name}", on_click=reset_cloze, args=(name, len(order)))
    if ss[checked_key]:
        right = 0
        for i, (_, surface) in enumerate(order):
            if ss[f"w_cloze_{name}_{i}"] == surface:
                right += 1
                st.write(f"({i + 1}) ✅ {surface}")
            else:
                st.write(f"({i + 1}) ❌ 정답: **{surface}**")
        st.info(f"결과: {right} / {len(order)}")


def reading_single(name, show_marks):
    st.caption(PASSAGES[name]["note"])
    ss.setdefault("w_read_act", ACT_READ)
    act = st.radio("활동", [ACT_READ, ACT_CLOZE], key="w_read_act", horizontal=True)
    if act == ACT_READ:
        show_html(render_parts(passage_parts(name), show_marks))
        speak_bar([("🔊 지문 듣기", " ".join(strip_marks(b) for b in PASSAGES[name]["beats"]))])
        with st.expander("🔑 이 지문의 핵심 단어"):
            st.dataframe(keyword_table(name), hide_index=True, use_container_width=True)
    else:
        reading_cloze(name, show_marks)


def reading_compare(show_marks):
    st.caption("같은 장면을 세 가지 어휘 수준으로 비교해 보세요.")
    for i, label in enumerate(BEAT_LABELS):
        st.markdown(f"**{label}**")
        for name in LEVEL_NAMES:
            body = render_parts(parse_marks(PASSAGES[name]["beats"][i]), show_marks)
            st.markdown(f"<div style='margin:2px 0 8px;line-height:1.9;'>"
                        f"<span style='opacity:.6;font-size:.8rem;'>{html.escape(name)}</span><br>{body}</div>",
                        unsafe_allow_html=True)
        st.divider()


def page_reading():
    st.subheader(STORY_TITLE)
    st.caption("같은 이야기를 초등 / 중·고등 / 확장 어휘 수준으로 읽어 보세요. 노란색은 그 수준의 단어예요.")
    with st.expander("📝 줄거리 (한국어)"):
        st.write(STORY_SUMMARY_KO)
    ss.setdefault("w_read_view", LEVEL_NAMES[0])
    ss.setdefault("w_read_marks", True)
    view = st.radio("지문 선택", [*LEVEL_NAMES, COMPARE], key="w_read_view", horizontal=True)
    show_marks = st.checkbox("수준 단어 노란색으로 표시", key="w_read_marks")
    st.divider()
    if view == COMPARE:
        reading_compare(show_marks)
    else:
        reading_single(view, show_marks)


# ───────────────────────── ⭐ 내 단어 ─────────────────────────
def page_mine():
    kinds = [("star", "⭐ 저장한 단어"), ("missed", "❌ 틀린 단어"), ("known", "✅ 외운 단어")]
    for tab, (kind, title) in zip(st.tabs([t for _, t in kinds]), kinds):
        with tab:
            m = marks(kind)
            words = [w for w in ALL if w in m]
            if not words:
                st.info("아직 단어가 없어요.")
                continue
            rows = [{"단어": w, "수준": W[w]["level"], "품사": pos_label(w), "뜻": W[w]["k"],
                     **({"틀린 횟수": m[w]} if kind == "missed" else {})} for w in words]
            st.dataframe(rows, hide_index=True, use_container_width=True)
            if kind in ("star", "missed"):
                x, y = st.columns(2)
                if x.button("🃏 카드로 공부", key=f"mc_{kind}", use_container_width=True):
                    ss.sel.update(src=kind, setno=0)
                    start_cards()
                    go("cards")
                    st.rerun()
                if y.button("📝 퀴즈 풀기", key=f"mq_{kind}", use_container_width=True):
                    ss.sel.update(src=kind, setno=0)
                    start_quiz()
                    go("quiz")
                    st.rerun()
            rm = st.multiselect("목록에서 빼기", words, key=f"rm_{kind}")
            if rm and st.button("빼기", key=f"rmb_{kind}"):
                for w in rm:
                    unmark(w, kind)
                st.rerun()


# ───────────────────────── 로그인 / 라우터 ─────────────────────────
def page_login():
    st.title("✉️ Mailroom English Plus")
    st.write("교육과정 기본 어휘를 내가 고른 순서대로 공부해요. 로그인하면 저장·외운·틀린 단어가 계정에 남아요.")
    t1, t2, t3 = st.tabs(["로그인", "새로 가입", "게스트"])
    with t1, st.form("login"):
        u, p = st.text_input("ID"), st.text_input("비밀번호", type="password")
        if st.form_submit_button("로그인"):
            if db_verify(u, p):
                ss.user = u.strip()
                st.rerun()
            else:
                st.error("ID 또는 비밀번호가 맞지 않아요.")
    with t2, st.form("reg"):
        u = st.text_input("ID (2~16자)")
        p = st.text_input("비밀번호 (4자 이상)", type="password")
        if st.form_submit_button("가입하기"):
            err = db_register(u, p)
            if err:
                st.error(err)
            else:
                ss.user = u.strip()
                st.rerun()
    with t3:
        st.write("가입 없이 바로 써 볼 수 있어요. 표시한 단어는 창을 닫으면 사라져요.")
        if st.button("게스트로 시작"):
            ss.user = GUEST
            st.rerun()


PAGES = {"home": "🏠 시작", "cards": "🃏 카드", "quiz": "📝 퀴즈", "list": "📋 목록",
         "read": "📖 읽기", "mine": "⭐ 내 단어"}
ROUTES = {"home": page_home, "cards": page_cards, "quiz": page_quiz, "list": page_list,
          "read": page_reading, "mine": page_mine}


def sidebar():
    with st.sidebar:
        st.write("👤 **게스트**" if U == GUEST else f"👤 **{U}**")
        if st.button("로그아웃"):
            for k in ("user", "fc", "qz", "diag_result"):
                ss[k] = None
            ss.diag_state, ss.gm = "intro", {}
            st.rerun()
        known = marks("known")
        st.subheader("내 학습 현황")
        for n in LEVEL_NAMES:
            st.write(f"**{n}** · 외운 단어 {sum(w in known for w in LEVEL_WORDS[n])} / {len(LEVEL_WORDS[n]):,}")
        if ss.diag_result:
            st.write(f"🧭 추천 수준: **{ss.diag_result['recommended']}**")
        st.subheader("🔊 음성")
        ss.accent = st.radio("발음", ["US", "GB"], index=["US", "GB"].index(ss.accent), horizontal=True,
                             format_func={"US": "미국식", "GB": "영국식"}.get)
        ss.rate = st.slider("속도", 0.5, 2.0, float(ss.rate), 0.1)
        if U == GUEST:
            st.caption("게스트 모드: 새로고침하면 기록이 사라져요.")


def main():
    apply_style()
    if not ss.user:
        page_login()
        return
    # 다른 페이지에 다녀와도 위젯 값(w_ 로 시작하는 키)이 사라지지 않게 유지
    for key in list(ss.keys()):
        if key.startswith("w_"):
            ss[key] = ss[key]
    st.title("✉️ Mailroom English Plus")
    sidebar()
    if ss.get("nav"):  # 메뉴 위젯을 만들기 전에 프로그램으로 이동해야 함
        ss.page = ss.pop("nav")
    st.radio("메뉴", list(PAGES), key="page", format_func=PAGES.get, horizontal=True, label_visibility="collapsed")
    ROUTES[ss.page]()


main()
