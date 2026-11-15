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
  - 단어 3,000개(2022 개정 교육과정 기본 어휘)가 이 파일 안에 내장되어 있어서 CSV가 필요 없어요.
  - 깃허브에는 app.py 하나만 올리면 됩니다.
  - requirements.txt:  streamlit  /  pandas
실행:  streamlit run app.py
"""
import base64
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
import zlib
import urllib.request
from pathlib import Path

import pandas as pd
import streamlit as st
import streamlit.components.v1 as components

st.set_page_config(page_title="Mailroom English Plus", page_icon="✉️", layout="centered")

# 화면 이름 -> 원본 Level 값
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


# ───────────────────────── 내장 단어 데이터 (Voca_3000.xlsx, 3,000개) ─────────────────────────
# 각 항목: [번호, 단어, 수준(E=초등/M=중·고등/X=확장), 뜻, 변형 표기]  (zlib + base64)
_PACK = (
    "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"
    "xqSuRf6v/wP6Lg8G"
)


# ───────────────────────── 데이터 ─────────────────────────
@st.cache_data
def load_words():
    code_to_name = {"E": "초등", "M": "중·고등", "X": "확장"}
    rows = json.loads(zlib.decompress(base64.b64decode(_PACK)).decode("utf-8"))
    words = {}
    for no, w, lv, k, var in rows:
        if w in words:  # 같은 철자가 여러 번 나오면 뜻을 합침
            if k and k not in words[w]["k"]:
                words[w]["k"] += "; " + k
            continue
        words[w] = dict(w=w, no=no, level=code_to_name[lv], k=k, var=var, pos=guess_pos(w, k))
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
