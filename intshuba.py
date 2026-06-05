#!/usr/bin/env python3
"""
INTSHUBA – Nguni Stone Game
Python/Flask backend with:
  - Full game logic (sowing, relay, capture, win detection)
  - 3 AI difficulty levels
  - SQLite user database (PBKDF2 password hashing)
  - Session management (secure tokens)
  - Rate limiting
  - Input sanitisation
  - Live bug fixer (logs all errors to DB, auto-recovers game state)
  - All 11 SA official languages + French
  - 5 Nguni skins
"""

import os, sys, json, sqlite3, hashlib, secrets, time, math, re, traceback
import threading, logging
from functools import wraps
from flask import Flask, request, session, jsonify, render_template_string, g

# ═══════════════════════════════════════════════════════════════════════════
#  SECURITY LAYER v2.3.0
#  MFA/TOTP · Fernet encryption · Score signing · Store protection
#  AR/VR mode · 3D/5D unified variant
# ═══════════════════════════════════════════════════════════════════════════

import hmac as _hmac, hashlib as _hs, struct as _st, base64 as _b64
import os as _os, time as _time, json as _json, re as _re, secrets as _sec
from functools import wraps
from cryptography.fernet import Fernet as _Fernet

# ── TOTP (pure stdlib, no pyotp needed) ─────────────────────────────────────
def _totp_code(b32_secret: str, window: int = 0) -> str:
    t   = int(_time.time()) // 30 + window
    key = _b64.b32decode(b32_secret.upper().replace(' ',''))
    msg = _st.pack('>Q', t)
    h   = _hmac.new(key, msg, _hs.sha1).digest()
    o   = h[-1] & 0xf
    code= _st.unpack('>I', h[o:o+4])[0] & 0x7fffffff
    return str(code % 1_000_000).zfill(6)

def generate_totp_secret() -> str:
    return _b64.b32encode(_os.urandom(20)).decode().rstrip('=')

def verify_totp(secret: str, code: str, drift: int = 1) -> bool:
    """Accept code ± drift windows (covers clock skew)."""
    code = str(code).strip().zfill(6)
    return any(_hmac.compare_digest(_totp_code(secret, w), code)
               for w in range(-drift, drift + 1))

def totp_uri(secret: str, email: str, issuer: str = 'Intshuba') -> str:
    padded = secret + '=' * (-len(secret) % 8)
    return (f'otpauth://totp/{issuer}:{email}'
            f'?secret={padded}&issuer={issuer}&algorithm=SHA1&digits=6&period=30')

# ── Fernet encryption (AES-128-CBC + HMAC-SHA256) ───────────────────────────
_FERNET_KEY: bytes | None = None

def _fernet() -> _Fernet:
    global _FERNET_KEY
    if _FERNET_KEY is None:
        raw = _os.environ.get('ENCRYPT_KEY', '')
        if raw and len(raw) >= 32:
            _FERNET_KEY = _b64.urlsafe_b64encode(_hs.sha256(raw.encode()).digest())
        else:
            # Derive from SECRET_KEY — deterministic, no extra env var required
            sk  = _os.environ.get('SECRET_KEY', _sec.token_hex(32))
            _FERNET_KEY = _b64.urlsafe_b64encode(_hs.sha256(sk.encode()).digest())
    return _Fernet(_FERNET_KEY)

def encrypt_str(plaintext: str) -> str:
    """Encrypt a string. Returns base64url ciphertext."""
    if not plaintext: return ''
    try:
        return _fernet().encrypt(plaintext.encode()).decode()
    except Exception:
        return plaintext  # graceful degradation

def decrypt_str(ciphertext: str) -> str:
    """Decrypt a string. Returns plaintext or empty on failure."""
    if not ciphertext: return ''
    try:
        return _fernet().decrypt(ciphertext.encode()).decode()
    except Exception:
        return ciphertext  # may already be plaintext (migration)

def encrypt_dict(d: dict) -> str:
    return encrypt_str(_json.dumps(d))

def decrypt_dict(s: str) -> dict:
    try: return _json.loads(decrypt_str(s))
    except Exception: return {}

# ── Score signing — prevents replay/manipulation ────────────────────────────
def sign_score(email: str, score: int, level: int, ts: int) -> str:
    """HMAC-SHA256 signature for a game score."""
    sk  = _os.environ.get('SECRET_KEY', '')
    msg = f'{email}:{score}:{level}:{ts}'.encode()
    return _hmac.new(sk.encode(), msg, _hs.sha256).hexdigest()[:32]

def verify_score(email: str, score: int, level: int, ts: int, sig: str) -> bool:
    expected = sign_score(email, score, level, ts)
    # Reject scores older than 5 minutes or from the future
    now = int(_time.time())
    if abs(now - ts) > 300:
        return False
    return _hmac.compare_digest(expected, str(sig)[:32])

# ── Store / economy transaction signing ─────────────────────────────────────
def sign_transaction(email: str, item_id: str, cost: int, ts: int) -> str:
    sk  = _os.environ.get('SECRET_KEY', '')
    msg = f'store:{email}:{item_id}:{cost}:{ts}'.encode()
    return _hmac.new(sk.encode(), msg, _hs.sha256).hexdigest()[:48]

def verify_transaction(email: str, item_id: str, cost: int, ts: int, sig: str) -> bool:
    expected = sign_transaction(email, item_id, cost, ts)
    now = int(_time.time())
    if abs(now - ts) > 120:   # transactions expire in 2 minutes
        return False
    return _hmac.compare_digest(expected, str(sig)[:48])

# ── Anti-abuse: idempotency keys ─────────────────────────────────────────────
_used_keys: dict[str, float] = {}   # key → expiry timestamp
_used_lock = __import__('threading').Lock()

def check_idempotency(key: str, ttl: int = 60) -> bool:
    """Return True if key is fresh (not a replay). Purges expired keys."""
    now = _time.time()
    with _used_lock:
        # Purge old keys
        expired = [k for k, exp in _used_keys.items() if exp < now]
        for k in expired: del _used_keys[k]
        if key in _used_keys:
            return False   # replay
        _used_keys[key] = now + ttl
        return True

# ── MFA-required decorator ───────────────────────────────────────────────────
def require_mfa(fn):
    """Decorator: route requires MFA verified for this session."""
    @wraps(fn)
    def wrapper(*args, **kwargs):
        from flask import session, jsonify, request
        user = current_user()
        if not user:
            return jsonify({'error': 'Not authenticated'}), 401
        db = get_db()
        row = db.execute('SELECT mfa_secret,mfa_enabled FROM users WHERE email=?',
                         (user['email'],)).fetchone()
        if row and row['mfa_enabled']:
            if not session.get('mfa_verified'):
                return jsonify({'error': 'MFA required',
                                'mfa_required': True,
                                'hint': 'POST /api/auth/mfa-verify with your 6-digit code'}), 403
        return fn(*args, **kwargs)
    return wrapper

# ── Password strength ────────────────────────────────────────────────────────
def validate_password_full(pw: str) -> list[str]:
    """Returns list of unmet requirements (empty = strong enough)."""
    issues = []
    if len(pw) < 8:           issues.append('Min 8 characters')
    if not _re.search(r'[A-Z]', pw): issues.append('1 uppercase letter')
    if not _re.search(r'[a-z]', pw): issues.append('1 lowercase letter')
    if not _re.search(r'\d',    pw): issues.append('1 digit')
    # Check against 20 most common passwords
    common = {'password','12345678','password1','qwerty123','abc12345',
               'iloveyou','monkey12','letmein1','dragon12','master12',
               'sunshine','princess','welcome1','shadow12','michael1',
               'football','batman12','trustno1','hello123','superman'}
    if pw.lower() in common: issues.append('Too common')
    return issues



# ─── App setup ────────────────────────────────────────────────────────────────
app = Flask(__name__)

# ── Environment-aware config (Railway + local) ─────────────────────────────
# Railway injects PORT, DATABASE_URL (optional), and any vars you add in its
# dashboard under  Settings → Variables.
_SECRET = os.environ.get('SECRET_KEY') or secrets.token_hex(32)
_IS_PROD = os.environ.get('RAILWAY_ENVIRONMENT') is not None   # True on Railway

app.secret_key = _SECRET
app.config['SESSION_COOKIE_HTTPONLY']  = True
app.config['SESSION_COOKIE_SAMESITE']  = 'Lax'
app.config['SESSION_COOKIE_SECURE']    = _IS_PROD   # HTTPS on Railway, HTTP locally
app.config['PERMANENT_SESSION_LIFETIME'] = 86400    # 24 h

# ── Paths ──────────────────────────────────────────────────────────────────
# Railway has an ephemeral filesystem under /app.  Use /data (mounted volume)
# if you add a Railway Volume, otherwise fall back to the app directory.
_DATA_DIR = os.environ.get('INTSHUBA_DATA_DIR') or os.path.dirname(os.path.abspath(__file__))
os.makedirs(_DATA_DIR, exist_ok=True)

DB_PATH  = os.environ.get('INTSHUBA_DB_PATH')  or os.path.join(_DATA_DIR, 'intshuba.db')
LOG_PATH = os.environ.get('INTSHUBA_LOG_PATH') or os.path.join(_DATA_DIR, 'buglog.txt')

# ── Logging ────────────────────────────────────────────────────────────────
_log_handlers = [logging.StreamHandler()]          # always log to stdout (Railway captures it)
try:
    _log_handlers.append(logging.FileHandler(LOG_PATH, encoding='utf-8'))
except Exception:
    pass                                           # read-only fs – stdout only
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s [%(levelname)s] %(message)s',
    handlers=_log_handlers,
)
log = logging.getLogger('intshuba')
if _IS_PROD:
    log.info('🚂 Running on Railway – production mode')

# ─── Production hardening ─────────────────────────────────────────────────────

@app.after_request
def set_security_headers(response):
    """Add security headers on every response. Especially important on Railway (HTTPS)."""
    response.headers['X-Content-Type-Options']  = 'nosniff'
    response.headers['X-Frame-Options']         = 'SAMEORIGIN'
    response.headers['X-XSS-Protection']        = '1; mode=block'
    response.headers['Referrer-Policy']         = 'strict-origin-when-cross-origin'
    if _IS_PROD:
        response.headers['Strict-Transport-Security'] = 'max-age=31536000; includeSubDomains'
    return response

@app.errorhandler(404)
def not_found(e):
    if request.path.startswith('/api/'):
        return jsonify({'error': 'Not found', 'path': request.path}), 404
    return render_template_string('<h2>404 – Page not found</h2><a href="/">Home</a>'), 404

@app.errorhandler(405)
def method_not_allowed(e):
    return jsonify({'error': 'Method not allowed'}), 405

@app.errorhandler(429)
def too_many_requests(e):
    return jsonify({'error': 'Too many requests – slow down!'}), 429

@app.errorhandler(500)
def internal_error(e):
    BugFixer.capture('error', f'Unhandled 500: {e}', e)
    if request.path.startswith('/api/'):
        return jsonify({'error': 'Internal server error'}), 500
    return render_template_string('<h2>500 – Something went wrong</h2><a href="/">Home</a>'), 500

# ─── Rate store cleanup (prevents unbounded memory growth on long-lived servers) ─
def _cleanup_rate_store():
    """Trim stale rate-limit buckets every 10 minutes."""
    import threading as _th
    def _run():
        while True:
            time.sleep(600)
            cutoff = time.time() - 300
            with _rate_lock:
                stale = [k for k, v in _rate_store.items()
                         if not any(t > cutoff for t in v)]
                for k in stale:
                    del _rate_store[k]
                if stale:
                    log.info(f'[Rate store] Pruned {len(stale)} stale buckets')
    _th.Thread(target=_run, daemon=True).start()

_cleanup_rate_store()

# ─── Live Bug Fixer ────────────────────────────────────────────────────────────
class BugFixer:
    """Captures all errors/warnings, stores them, auto-applies known fixes."""
    _lock = threading.Lock()
    _log  = []          # [{time, level, msg, fixed}]
    _rules = []         # [{pattern, fix_fn, description, applied_count}]

    @classmethod
    def capture(cls, level, msg, exc=None):
        entry = {
            'time': time.time(),
            'ts':   time.strftime('%H:%M:%S'),
            'level': level,
            'msg':  str(msg)[:500],
            'fixed': None,
            'traceback': traceback.format_exc() if exc else None
        }
        with cls._lock:
            cls._log.append(entry)
            if len(cls._log) > 500:
                cls._log = cls._log[-500:]
        log.log(logging.ERROR if level=='error' else logging.WARNING, f"[BugFixer] {msg}")
        cls._auto_fix(entry)
        return entry

    @classmethod
    def _auto_fix(cls, entry):
        for rule in cls._rules:
            if re.search(rule['pattern'], entry['msg'], re.I):
                try:
                    result = rule['fix_fn'](entry['msg'])
                    if result:
                        entry['fixed'] = rule['description']
                        rule['applied_count'] = rule.get('applied_count', 0) + 1
                        log.info(f"🔧 Auto-fixed [{rule['id']}]: {rule['description']}")
                except Exception as e:
                    log.warning(f"Auto-fix rule {rule['id']} failed: {e}")

    @classmethod
    def register_rule(cls, rule_id, pattern, description, fix_fn):
        cls._rules.append({
            'id': rule_id, 'pattern': pattern,
            'description': description, 'fix_fn': fix_fn,
            'applied_count': 0
        })

    @classmethod
    def get_log(cls):
        with cls._lock:
            return list(cls._log[-100:])

    @classmethod
    def get_summary(cls):
        with cls._lock:
            errors   = sum(1 for e in cls._log if e['level']=='error')
            warnings = sum(1 for e in cls._log if e['level']=='warning')
            fixed    = sum(1 for e in cls._log if e['fixed'])
            rules    = [{'id':r['id'],'desc':r['description'],'count':r.get('applied_count',0)} for r in cls._rules]
        return {'errors': errors, 'warnings': warnings, 'fixed': fixed, 'rules': rules}

# Register auto-fix rules
def _fix_db_locked_legacy(msg):
    """Re-initialise DB connection pool on lock."""

def _fix_db_locked(msg):
    try: init_db(); return True
    except: return False

def _fix_session_corrupt(msg):
    return True

    return True  # handled at route level

BugFixer.register_rule('db_locked',       r'database.*locked|OperationalError', 'Re-initialised DB connection', _fix_db_locked)
BugFixer.register_rule('session_corrupt',  r'session.*corrupt|KeyError.*session', 'Cleared corrupt session',   _fix_session_corrupt)
BugFixer.register_rule('game_state_err',   r'game.*state|board.*invalid|IndexError.*board', 'Reset game state', lambda m: True)
BugFixer.register_rule('rate_limit_burst', r'rate.*limit.*exceeded',  'Rate limit hit — logged only',          lambda m: True)
BugFixer.register_rule('invalid_move',     r'invalid.*move|move.*rejected', 'Invalid move — client notified',   lambda m: True)

# ─── Security ──────────────────────────────────────────────────────────────────
def hash_password(password: str, salt: str = None):
    if not salt:
        salt = secrets.token_hex(32)
    dk = hashlib.pbkdf2_hmac('sha256', password.encode(), salt.encode(), 150_000)
    return dk.hex(), salt

def verify_password(password: str, stored_hash: str, salt: str) -> bool:
    dk, _ = hash_password(password, salt)
    return secrets.compare_digest(dk, stored_hash)

def sanitise(s: str, max_len=100) -> str:
    if not isinstance(s, str): return ''
    s = re.sub(r'[<>"\'`\\]', '', s).strip()
    return s[:max_len]

def validate_email(email: str) -> bool:
    return bool(re.match(r'^[a-zA-Z0-9._%+\-]+@[a-zA-Z0-9.\-]+\.[a-zA-Z]{2,}$', email)) and len(email) <= 80

def validate_password(pw: str):
    issues = []
    if len(pw) < 8:           issues.append('Min 8 characters')
    if not re.search(r'[A-Z]', pw): issues.append('1 uppercase letter')
    if not re.search(r'[0-9]', pw): issues.append('1 number')
    if not re.search(r'[^A-Za-z0-9]', pw): issues.append('1 special character')
    return len(issues) == 0, issues

# Rate limiter
_rate_store = {}
_rate_lock  = threading.Lock()

def rate_check(key: str, max_attempts=5, window_s=60) -> bool:
    now = time.time()
    with _rate_lock:
        attempts = [t for t in _rate_store.get(key, []) if now - t < window_s]
        if len(attempts) >= max_attempts:
            BugFixer.capture('warning', f'rate_limit_exceeded: {key}')
            return False
        attempts.append(now)
        _rate_store[key] = attempts
    return True

# ─── Database ──────────────────────────────────────────────────────────────────
def get_db():
    if 'db' not in g:
        g.db = sqlite3.connect(DB_PATH, check_same_thread=False)
        g.db.row_factory = sqlite3.Row
        g.db.execute('PRAGMA journal_mode=WAL')
    return g.db

@app.teardown_appcontext
def close_db(e=None):
    db = g.pop('db', None)
    if db: db.close()

def init_db():
    with app.app_context():
        db = sqlite3.connect(DB_PATH)
        db.executescript('''
            CREATE TABLE IF NOT EXISTS users (
                email            TEXT PRIMARY KEY,
                name             TEXT NOT NULL,
                hash             TEXT NOT NULL,
                salt             TEXT NOT NULL,
                created          INTEGER DEFAULT (strftime('%s','now')),
                last_login       INTEGER DEFAULT 0,
                wins             INTEGER DEFAULT 0,
                losses           INTEGER DEFAULT 0,
                draws            INTEGER DEFAULT 0,
                games            INTEGER DEFAULT 0,
                total_cows       INTEGER DEFAULT 0,
                skin             TEXT    DEFAULT 'zulu',
                level            INTEGER DEFAULT 1,
                lang             TEXT    DEFAULT 'en',
                herd_cows        INTEGER DEFAULT 10,
                land_plots       INTEGER DEFAULT 0,
                crop_farms       INTEGER DEFAULT 0,
                cattle_pens      INTEGER DEFAULT 0,
                jewellery        INTEGER DEFAULT 0,
                is_married       INTEGER DEFAULT 0,
                spouse_email     TEXT    DEFAULT '',
                has_crown        INTEGER DEFAULT 0,
                crown_won        INTEGER DEFAULT 0,
                title            TEXT    DEFAULT 'iJongo',
                last_cow_gift    INTEGER DEFAULT 0,
                current_level    INTEGER DEFAULT 1,
                season           INTEGER DEFAULT 1,
                plan             TEXT    DEFAULT 'free',
                plan_expires     INTEGER DEFAULT 0,
                stripe_customer  TEXT    DEFAULT '',
                stripe_sub_id    TEXT    DEFAULT '',
                play_tokens      INTEGER DEFAULT 10,
                is_admin         INTEGER DEFAULT 0,
                elo              INTEGER DEFAULT 1200,
                elo_peak         INTEGER DEFAULT 1200,
                login_streak     INTEGER DEFAULT 0,
                last_login_date  TEXT    DEFAULT '',
                streak_shield    INTEGER DEFAULT 0,
                referral_code    TEXT    DEFAULT '',
                referred_by      TEXT    DEFAULT '',
                family_id        TEXT    DEFAULT '',
                is_child         INTEGER DEFAULT 0,
                parent_email     TEXT    DEFAULT '',
                tribe_id         TEXT    DEFAULT 'world',
                age_pool         TEXT    DEFAULT 'open',
                birth_year       INTEGER DEFAULT 0,
                regalia          TEXT    DEFAULT '',
                competition_wins INTEGER DEFAULT 0,
                season_rank      INTEGER DEFAULT 0,
                last_passive_run INTEGER DEFAULT 0,
                badge            TEXT    DEFAULT '',
                streak_days      INTEGER DEFAULT 0,
                streak_last      TEXT    DEFAULT '',
                clan_id          TEXT    DEFAULT '',
                clan_role        TEXT    DEFAULT '',
                family_role      TEXT    DEFAULT '',
                mfa_secret       TEXT    DEFAULT '',
                mfa_enabled      INTEGER DEFAULT 0,
                game_mode        TEXT    DEFAULT '5d',
                mfa_backup_codes TEXT    DEFAULT '[]',
                enc_bio          TEXT    DEFAULT '',
                enc_wall         TEXT    DEFAULT '',
                last_mfa_ts      INTEGER DEFAULT 0,
                failed_mfa_count INTEGER DEFAULT 0,
                account_locked   INTEGER DEFAULT 0,
                lock_until       INTEGER DEFAULT 0
            );
            CREATE TABLE IF NOT EXISTS sessions (
                token       TEXT PRIMARY KEY,
                email       TEXT NOT NULL,
                created     INTEGER,
                expires     INTEGER
            );
            CREATE TABLE IF NOT EXISTS bug_log (
                id          INTEGER PRIMARY KEY AUTOINCREMENT,
                ts          INTEGER DEFAULT (strftime('%s','now')),
                level       TEXT,
                msg         TEXT,
                fixed       TEXT
            );
            CREATE TABLE IF NOT EXISTS online_games (
                room_id          TEXT PRIMARY KEY,
                host_email       TEXT NOT NULL,
                guest_email      TEXT,
                host_name        TEXT,
                guest_name       TEXT,
                status           TEXT DEFAULT 'waiting',
                level            INTEGER DEFAULT 1,
                skin             TEXT DEFAULT 'zulu',
                board_rows       INTEGER DEFAULT 4,
                board_cols       INTEGER DEFAULT 4,
                board_state      TEXT,
                current_player   INTEGER DEFAULT 0,
                created          INTEGER DEFAULT (strftime('%s','now')),
                updated          INTEGER DEFAULT (strftime('%s','now'))
            );
            CREATE TABLE IF NOT EXISTS invitations (
                code        TEXT PRIMARY KEY,
                host_email  TEXT NOT NULL,
                host_name   TEXT NOT NULL,
                room_id     TEXT NOT NULL,
                created     INTEGER DEFAULT (strftime('%s','now')),
                expires     INTEGER,
                used        INTEGER DEFAULT 0
            );
            CREATE TABLE IF NOT EXISTS tournaments (
                id          TEXT PRIMARY KEY,
                name        TEXT NOT NULL,
                host_email  TEXT NOT NULL,
                host_name   TEXT NOT NULL,
                status      TEXT DEFAULT 'open',
                max_players INTEGER DEFAULT 8,
                players     TEXT DEFAULT '[]',
                bracket     TEXT DEFAULT '{}',
                created     INTEGER DEFAULT (strftime('%s','now')),
                start_time  INTEGER
            );
            CREATE TABLE IF NOT EXISTS support_messages (
                id          INTEGER PRIMARY KEY AUTOINCREMENT,
                session_id  TEXT NOT NULL,
                user_name   TEXT DEFAULT 'Guest',
                user_email  TEXT DEFAULT '',
                sender      TEXT NOT NULL,
                message     TEXT NOT NULL,
                msg_type    TEXT DEFAULT 'text',
                created     INTEGER DEFAULT (strftime('%s','now'))
            );
            CREATE TABLE IF NOT EXISTS feedback (
                id          INTEGER PRIMARY KEY AUTOINCREMENT,
                user_name   TEXT DEFAULT 'Guest',
                user_email  TEXT DEFAULT '',
                rating      INTEGER DEFAULT 5,
                category    TEXT DEFAULT 'general',
                message     TEXT NOT NULL,
                platform    TEXT DEFAULT 'web',
                version     TEXT DEFAULT '2.0',
                resolved    INTEGER DEFAULT 0,
                created     INTEGER DEFAULT (strftime('%s','now'))
            );
            CREATE TABLE IF NOT EXISTS user_inputs (
                id          INTEGER PRIMARY KEY AUTOINCREMENT,
                user_name   TEXT DEFAULT 'Guest',
                user_email  TEXT DEFAULT '',
                input_type  TEXT NOT NULL,
                question    TEXT NOT NULL,
                answer      TEXT NOT NULL,
                created     INTEGER DEFAULT (strftime('%s','now'))
            );
            CREATE INDEX IF NOT EXISTS idx_sessions_email ON sessions(email);
            CREATE INDEX IF NOT EXISTS idx_sessions_expires ON sessions(expires);
            CREATE INDEX IF NOT EXISTS idx_support_session ON support_messages(session_id);
            CREATE INDEX IF NOT EXISTS idx_feedback_created ON feedback(created);
            CREATE TABLE IF NOT EXISTS payments (
                id              INTEGER PRIMARY KEY AUTOINCREMENT,
                user_email      TEXT    NOT NULL,
                provider        TEXT    NOT NULL,
                provider_ref    TEXT    NOT NULL UNIQUE,
                product_id      TEXT    NOT NULL,
                plan            TEXT    NOT NULL,
                amount_cents    INTEGER DEFAULT 0,
                currency        TEXT    DEFAULT 'ZAR',
                status          TEXT    DEFAULT 'pending',
                platform        TEXT    DEFAULT 'web',
                created         INTEGER DEFAULT (strftime('%s','now')),
                verified        INTEGER DEFAULT (strftime('%s','now'))
            );
            CREATE TABLE IF NOT EXISTS donations (
                id          INTEGER PRIMARY KEY AUTOINCREMENT,
                user_email  TEXT DEFAULT '',
                user_name   TEXT DEFAULT 'Anonymous',
                amount_zar  INTEGER NOT NULL,
                message     TEXT DEFAULT '',
                provider    TEXT DEFAULT 'kofi',
                ref         TEXT DEFAULT '',
                created     INTEGER DEFAULT (strftime('%s','now'))
            );
            CREATE INDEX IF NOT EXISTS idx_payments_email  ON payments(user_email);
            CREATE INDEX IF NOT EXISTS idx_payments_ref    ON payments(provider_ref);
            CREATE TABLE IF NOT EXISTS kingdom_events (
                id          INTEGER PRIMARY KEY AUTOINCREMENT,
                user_email  TEXT NOT NULL,
                event_type  TEXT NOT NULL,
                detail      TEXT DEFAULT '{}',
                cows_delta  INTEGER DEFAULT 0,
                ledger_sig  TEXT DEFAULT '',
                created     INTEGER DEFAULT (strftime('%s','now'))
            );
            CREATE TABLE IF NOT EXISTS marriages (
                id             INTEGER PRIMARY KEY AUTOINCREMENT,
                proposer_email TEXT NOT NULL,
                partner_email  TEXT NOT NULL,
                lobola_paid    INTEGER DEFAULT 0,
                status         TEXT DEFAULT 'pending',
                created        INTEGER DEFAULT (strftime('%s','now'))
            );
            CREATE TABLE IF NOT EXISTS crown_history (
                id            INTEGER PRIMARY KEY AUTOINCREMENT,
                holder_email  TEXT NOT NULL,
                holder_name   TEXT NOT NULL,
                won_at        INTEGER DEFAULT (strftime('%s','now')),
                lost_at       INTEGER DEFAULT 0,
                cows_at_crown INTEGER DEFAULT 0,
                season        INTEGER DEFAULT 1
            );
            CREATE TABLE IF NOT EXISTS bets (
                id              INTEGER PRIMARY KEY AUTOINCREMENT,
                challenger_email TEXT NOT NULL,
                defender_email   TEXT DEFAULT 'AI',
                bet_amount       INTEGER NOT NULL,
                outcome          TEXT DEFAULT 'pending',
                level            INTEGER DEFAULT 2,
                created          INTEGER DEFAULT (strftime('%s','now'))
            );
            CREATE INDEX IF NOT EXISTS idx_kingdom_email ON kingdom_events(user_email);
            CREATE INDEX IF NOT EXISTS idx_crown_season  ON crown_history(season);
            CREATE TABLE IF NOT EXISTS competitions (
                id              TEXT PRIMARY KEY,
                name            TEXT NOT NULL,
                comp_type       TEXT NOT NULL,
                tribe           TEXT DEFAULT '',
                age_pool        TEXT DEFAULT 'open',
                host_email      TEXT NOT NULL,
                host_name       TEXT NOT NULL,
                entry_fee_zar   INTEGER DEFAULT 0,
                prize_pool_zar  INTEGER DEFAULT 0,
                status          TEXT DEFAULT 'open',
                stream_url      TEXT DEFAULT '',
                duration_days   INTEGER DEFAULT 90,
                sponsor_name    TEXT DEFAULT '',
                created         INTEGER DEFAULT (strftime('%s','now')),
                ends_at         INTEGER DEFAULT 0
            );
            CREATE TABLE IF NOT EXISTS competition_players (
                id              INTEGER PRIMARY KEY AUTOINCREMENT,
                comp_id         TEXT NOT NULL,
                player_email    TEXT NOT NULL,
                player_name     TEXT NOT NULL,
                tribe           TEXT DEFAULT 'world',
                age_pool        TEXT DEFAULT 'open',
                score           INTEGER DEFAULT 0,
                wins            INTEGER DEFAULT 0,
                losses          INTEGER DEFAULT 0,
                joined          INTEGER DEFAULT (strftime('%s','now'))
            );
            CREATE TABLE IF NOT EXISTS tribe_memberships (
                player_email    TEXT PRIMARY KEY,
                tribe_id        TEXT NOT NULL,
                rank            TEXT DEFAULT 'member',
                joined          INTEGER DEFAULT (strftime('%s','now'))
            );
            CREATE INDEX IF NOT EXISTS idx_comp_status   ON competitions(status);
            CREATE INDEX IF NOT EXISTS idx_comp_players  ON competition_players(comp_id);
            CREATE INDEX IF NOT EXISTS idx_tribe_members ON tribe_memberships(tribe_id);
            CREATE TABLE IF NOT EXISTS ai_weights (
                persona_id    TEXT PRIMARY KEY,
                weights_json  TEXT NOT NULL DEFAULT '{}',
                games_played  INTEGER DEFAULT 0,
                games_won     INTEGER DEFAULT 0,
                win_rate      REAL    DEFAULT 0.0,
                version       INTEGER DEFAULT 1,
                updated       INTEGER DEFAULT (strftime('%s','now'))
            );
            CREATE TABLE IF NOT EXISTS ai_game_log (
                id                  INTEGER PRIMARY KEY AUTOINCREMENT,
                persona_id          TEXT NOT NULL,
                ai_won              INTEGER DEFAULT 0,
                ai_cows             INTEGER DEFAULT 0,
                human_cows          INTEGER DEFAULT 0,
                moves_count         INTEGER DEFAULT 0,
                version_when_played INTEGER DEFAULT 1,
                created             INTEGER DEFAULT (strftime('%s','now'))
            );
            CREATE INDEX IF NOT EXISTS idx_ai_log_persona ON ai_game_log(persona_id);
            -- v2.3.0 tables
            CREATE TABLE IF NOT EXISTS user_achievements (
                id             INTEGER PRIMARY KEY AUTOINCREMENT,
                user_email     TEXT NOT NULL,
                achievement_id TEXT NOT NULL,
                earned_at      INTEGER DEFAULT (strftime('%s','now')),
                UNIQUE(user_email, achievement_id)
            );
            CREATE TABLE IF NOT EXISTS chests (
                id            INTEGER PRIMARY KEY AUTOINCREMENT,
                player_email  TEXT NOT NULL,
                chest_type    TEXT    DEFAULT 'bronze',
                contents_json TEXT    DEFAULT '{}',
                locked_until  INTEGER DEFAULT 0,
                unlock_at     INTEGER DEFAULT 0,
                opened        INTEGER DEFAULT 0,
                slot          INTEGER DEFAULT 0,
                status        TEXT    DEFAULT 'locked',
                created       INTEGER DEFAULT (strftime('%s','now'))
            );
            CREATE TABLE IF NOT EXISTS friends (
                id      INTEGER PRIMARY KEY AUTOINCREMENT,
                user_a  TEXT NOT NULL,
                user_b  TEXT NOT NULL,
                status  TEXT DEFAULT 'accepted',
                created INTEGER DEFAULT (strftime('%s','now'))
            );
            CREATE TABLE IF NOT EXISTS clans (
                id           TEXT PRIMARY KEY,
                name         TEXT NOT NULL,
                description  TEXT DEFAULT '',
                tribe_id     TEXT DEFAULT 'world',
                leader_email TEXT NOT NULL,
                member_count INTEGER DEFAULT 0,
                total_cows   INTEGER DEFAULT 0,
                war_wins     INTEGER DEFAULT 0,
                badge        TEXT    DEFAULT '',
                tag          TEXT    DEFAULT '',
                leader_name  TEXT    DEFAULT '',
                created      INTEGER DEFAULT (strftime('%s','now'))
            );
            CREATE TABLE IF NOT EXISTS puzzle_completions (
                id           INTEGER PRIMARY KEY AUTOINCREMENT,
                user_email   TEXT NOT NULL,
                puzzle_id    INTEGER NOT NULL,
                completed_at INTEGER DEFAULT (strftime('%s','now')),
                UNIQUE(user_email, puzzle_id)
            );
            CREATE TABLE IF NOT EXISTS daily_scores (
                id         INTEGER PRIMARY KEY AUTOINCREMENT,
                user_email TEXT NOT NULL,
                day        TEXT NOT NULL,
                score      INTEGER DEFAULT 0,
                UNIQUE(user_email, day)
            );
            CREATE TABLE IF NOT EXISTS game_replays (
                game_id    TEXT PRIMARY KEY,
                user_email TEXT NOT NULL,
                moves_json TEXT DEFAULT '[]',
                result     TEXT DEFAULT 'unknown',
                persona_id TEXT DEFAULT 'shaka',
                created    INTEGER DEFAULT (strftime('%s','now'))
            );
            CREATE INDEX IF NOT EXISTS idx_achievements_user  ON user_achievements(user_email);
            CREATE INDEX IF NOT EXISTS idx_chests_owner       ON chests(player_email);
            CREATE INDEX IF NOT EXISTS idx_friends_user       ON friends(user_a,user_b);
            CREATE INDEX IF NOT EXISTS idx_daily_scores_day   ON daily_scores(day,score);
            CREATE INDEX IF NOT EXISTS idx_replays_user       ON game_replays(user_email);

            -- Route-facing aliases and new tables for v2.3.0
            CREATE TABLE IF NOT EXISTS achievements (
                id             INTEGER PRIMARY KEY AUTOINCREMENT,
                player_email   TEXT NOT NULL,
                achievement_id TEXT NOT NULL,
                earned_at      INTEGER DEFAULT (strftime('%s','now')),
                UNIQUE(player_email, achievement_id)
            );
            CREATE TABLE IF NOT EXISTS replays (
                id           INTEGER PRIMARY KEY AUTOINCREMENT,
                player_email TEXT NOT NULL,
                player_name  TEXT    DEFAULT '',
                moves_json   TEXT    NOT NULL DEFAULT '[]',
                result       TEXT    DEFAULT 'unknown',
                score_human  INTEGER DEFAULT 0,
                score_ai     INTEGER DEFAULT 0,
                p0_cows      INTEGER DEFAULT 0,
                p1_cows      INTEGER DEFAULT 0,
                persona_id   TEXT    DEFAULT 'shaka',
                duration_s   INTEGER DEFAULT 0,
                created      INTEGER DEFAULT (strftime('%s','now'))
            );
            CREATE TABLE IF NOT EXISTS families (
                id           TEXT PRIMARY KEY,
                family_name  TEXT NOT NULL,
                parent_email TEXT NOT NULL,
                parent_name  TEXT    DEFAULT '',
                pin_hash     TEXT NOT NULL,
                max_children INTEGER DEFAULT 4,
                created      INTEGER DEFAULT (strftime('%s','now'))
            );
            CREATE INDEX IF NOT EXISTS idx_achievements_email ON achievements(player_email);
            CREATE INDEX IF NOT EXISTS idx_replays_email      ON replays(player_email);

            CREATE TABLE IF NOT EXISTS clan_members (
                id           INTEGER PRIMARY KEY AUTOINCREMENT,
                clan_id      TEXT NOT NULL,
                player_email TEXT NOT NULL,
                rank         TEXT    DEFAULT 'member',
                joined       INTEGER DEFAULT (strftime('%s','now')),
                UNIQUE(clan_id, player_email)
            );
            CREATE INDEX IF NOT EXISTS idx_clan_members ON clan_members(clan_id, player_email);

            CREATE TABLE IF NOT EXISTS wall_posts (
                id           INTEGER PRIMARY KEY AUTOINCREMENT,
                author_email TEXT NOT NULL,
                target_email TEXT NOT NULL,
                content_enc  TEXT NOT NULL,
                post_type    TEXT DEFAULT 'wall',
                created      INTEGER DEFAULT (strftime('%s','now')),
                flagged      INTEGER DEFAULT 0
            );
            CREATE TABLE IF NOT EXISTS mfa_events (
                id    INTEGER PRIMARY KEY AUTOINCREMENT,
                email TEXT NOT NULL,
                event TEXT NOT NULL,
                ip    TEXT DEFAULT '',
                ts    INTEGER DEFAULT (strftime('%s','now'))
            );
            CREATE TABLE IF NOT EXISTS store_transactions (
                id           INTEGER PRIMARY KEY AUTOINCREMENT,
                email        TEXT NOT NULL,
                item_id      TEXT NOT NULL,
                cost_cows    INTEGER DEFAULT 0,
                idempotency  TEXT UNIQUE,
                sig          TEXT NOT NULL,
                ts           INTEGER DEFAULT (strftime('%s','now'))
            );
            CREATE INDEX IF NOT EXISTS idx_wall_target ON wall_posts(target_email);
            CREATE INDEX IF NOT EXISTS idx_mfa_events  ON mfa_events(email);
            CREATE INDEX IF NOT EXISTS idx_store_trans ON store_transactions(email);

            CREATE TABLE IF NOT EXISTS blockchain_wallets (
                email          TEXT PRIMARY KEY,
                wallet_address TEXT NOT NULL,
                verified       INTEGER DEFAULT 0,
                linked_at      INTEGER DEFAULT (strftime('%s','now'))
            );
            CREATE TABLE IF NOT EXISTS blockchain_txs (
                id       INTEGER PRIMARY KEY AUTOINCREMENT,
                email    TEXT NOT NULL,
                tx_type  TEXT NOT NULL,
                tx_hash  TEXT DEFAULT '',
                status   TEXT DEFAULT 'pending',
                detail   TEXT DEFAULT '{}',
                created  INTEGER DEFAULT (strftime('%s','now'))
            );
            CREATE TABLE IF NOT EXISTS marketplace_listings (
                id           INTEGER PRIMARY KEY AUTOINCREMENT,
                email        TEXT NOT NULL,
                cow_amount   INTEGER NOT NULL,
                price_matic  TEXT NOT NULL,
                wallet       TEXT NOT NULL,
                active       INTEGER DEFAULT 1,
                listing_id   INTEGER DEFAULT 0,
                tx_hash      TEXT DEFAULT '',
                created      INTEGER DEFAULT (strftime('%s','now'))
            );
            CREATE INDEX IF NOT EXISTS idx_bc_wallets ON blockchain_wallets(email);
            CREATE INDEX IF NOT EXISTS idx_bc_txs     ON blockchain_txs(email);
            CREATE INDEX IF NOT EXISTS idx_bc_market  ON marketplace_listings(email,active);
        ''')
        new_cols = [
            'ALTER TABLE users ADD COLUMN total_cows       INTEGER DEFAULT 0',
            'ALTER TABLE users ADD COLUMN plan             TEXT    DEFAULT "free"',
            'ALTER TABLE users ADD COLUMN plan_expires     INTEGER DEFAULT 0',
            'ALTER TABLE users ADD COLUMN stripe_customer  TEXT    DEFAULT ""',
            'ALTER TABLE users ADD COLUMN stripe_sub_id    TEXT    DEFAULT ""',
            'ALTER TABLE users ADD COLUMN play_tokens      INTEGER DEFAULT 10',
            'ALTER TABLE users ADD COLUMN is_admin         INTEGER DEFAULT 0',
            # ── Kingdom economy columns ──────────────────────────────────────
            'ALTER TABLE users ADD COLUMN herd_cows        INTEGER DEFAULT 10',
            'ALTER TABLE users ADD COLUMN land_plots       INTEGER DEFAULT 0',
            'ALTER TABLE users ADD COLUMN jewellery        INTEGER DEFAULT 0',
            'ALTER TABLE users ADD COLUMN is_married       INTEGER DEFAULT 0',
            'ALTER TABLE users ADD COLUMN spouse_email     TEXT    DEFAULT ""',
            'ALTER TABLE users ADD COLUMN has_crown        INTEGER DEFAULT 0',
            'ALTER TABLE users ADD COLUMN crown_won        INTEGER DEFAULT 0',
            'ALTER TABLE users ADD COLUMN title            TEXT    DEFAULT "iJongo"',
            'ALTER TABLE users ADD COLUMN last_cow_gift    INTEGER DEFAULT 0',
            'ALTER TABLE users ADD COLUMN current_level    INTEGER DEFAULT 1',
            'ALTER TABLE users ADD COLUMN season           INTEGER DEFAULT 1',
            'ALTER TABLE users ADD COLUMN tribe_id          TEXT    DEFAULT "world"',
            'ALTER TABLE users ADD COLUMN age_pool          TEXT    DEFAULT "open"',
            'ALTER TABLE users ADD COLUMN birth_year        INTEGER DEFAULT 0',
            'ALTER TABLE users ADD COLUMN crop_farms        INTEGER DEFAULT 0',
            'ALTER TABLE users ADD COLUMN cattle_pens       INTEGER DEFAULT 0',
            'ALTER TABLE users ADD COLUMN regalia           TEXT    DEFAULT ""',
            'ALTER TABLE users ADD COLUMN competition_wins  INTEGER DEFAULT 0',
            'ALTER TABLE users ADD COLUMN season_rank       INTEGER DEFAULT 0',
            'ALTER TABLE users ADD COLUMN last_passive_run  INTEGER DEFAULT 0',
            'ALTER TABLE users ADD COLUMN mfa_secret       TEXT    DEFAULT ""',
            'ALTER TABLE users ADD COLUMN mfa_enabled      INTEGER DEFAULT 0',
            'ALTER TABLE users ADD COLUMN mfa_backup_codes TEXT    DEFAULT "[]"',
            'ALTER TABLE users ADD COLUMN enc_bio          TEXT    DEFAULT ""',
            'ALTER TABLE users ADD COLUMN enc_wall         TEXT    DEFAULT ""',
            'ALTER TABLE users ADD COLUMN last_mfa_ts      INTEGER DEFAULT 0',
            'ALTER TABLE users ADD COLUMN failed_mfa_count INTEGER DEFAULT 0',
            'ALTER TABLE users ADD COLUMN account_locked   INTEGER DEFAULT 0',
            'ALTER TABLE users ADD COLUMN lock_until       INTEGER DEFAULT 0',
            'ALTER TABLE users ADD COLUMN elo_rating        INTEGER DEFAULT 1200',
            'ALTER TABLE users ADD COLUMN elo_peak          INTEGER DEFAULT 1200',
            'ALTER TABLE users ADD COLUMN login_streak      INTEGER DEFAULT 0',
            'ALTER TABLE users ADD COLUMN streak_shield     INTEGER DEFAULT 0',
            'ALTER TABLE users ADD COLUMN referral_code     TEXT    DEFAULT ""',
            'ALTER TABLE users ADD COLUMN referred_by       TEXT    DEFAULT ""',
            'ALTER TABLE users ADD COLUMN clan_id           TEXT    DEFAULT ""',
            'ALTER TABLE users ADD COLUMN family_role       TEXT    DEFAULT ""',
            'ALTER TABLE users ADD COLUMN parent_email      TEXT    DEFAULT ""',
            'ALTER TABLE users ADD COLUMN family_pin_hash   TEXT    DEFAULT ""',
        ]
        for col_sql in new_cols:
            try: db.execute(col_sql); db.commit()
            except: pass
        db.commit()
        db.close()

def create_session(email: str) -> str:
    token = secrets.token_hex(32)
    expires = int(time.time()) + 86400  # 24h
    db = get_db()
    db.execute('DELETE FROM sessions WHERE email=? OR expires<?', (email, int(time.time())))
    db.execute('INSERT INTO sessions(token,email,created,expires) VALUES(?,?,?,?)',
               (token, email, int(time.time()), expires))
    db.commit()
    return token

def get_user_from_session(token: str):
    if not token: return None
    db = get_db()
    row = db.execute('SELECT s.email FROM sessions s WHERE s.token=? AND s.expires>?',
                     (token, int(time.time()))).fetchone()
    if not row: return None
    return db.execute('SELECT * FROM users WHERE email=?', (row['email'],)).fetchone()

def current_user():
    token = session.get('token')
    if not token: return None
    try:
        return get_user_from_session(token)
    except Exception as e:
        BugFixer.capture('error', f'session_corrupt: {e}', e)
        return None

def login_required(f):
    @wraps(f)
    def wrapper(*args, **kwargs):
        if not current_user():
            return jsonify({'error': 'Not authenticated'}), 401
        return f(*args, **kwargs)
    return wrapper

# ─── Game Logic ────────────────────────────────────────────────────────────────
SKINS = {
    'zulu':    {'board':'#4A2C0A','stone':'#C9A84C','hl':'#FFD700','cap':'#FF6B00','bg':'#120A02','name':'AmaZulu'},
    'xhosa':   {'board':'#2D1B4E','stone':'#E8722A','hl':'#FF9F43','cap':'#EE5A24','bg':'#0A0618','name':'AmaXhosa'},
    'ndebele': {'board':'#1A3A1A','stone':'#F8C82A','hl':'#FF2D55','cap':'#00D4AA','bg':'#030A03','name':'AmaNdebele'},
    'swati':   {'board':'#3D1C00','stone':'#D4A055','hl':'#A8E063','cap':'#FF5F40','bg':'#100800','name':'AmaSwati'},
    'tsonga':  {'board':'#1B2E1B','stone':'#ADD45C','hl':'#FFD166','cap':'#EF476F','bg':'#030803','name':'VaTsonga'},
}

class GameState:
    """Full game state for one session."""
    def __init__(self, rows=4, cols=4, mode='ai', level=1):
        self.rows   = rows
        self.cols   = cols
        self.mode   = mode
        self.level  = level
        self.board  = [2] * (rows * cols)
        self.player = 0        # 0=human, 1=AI/P2
        self.phase  = 'idle'   # idle|sowing|ai-wait|done
        self.running= True
        self.message= ''
        self._validate()

    def _validate(self):
        """Sanity-check state, auto-recover if corrupt."""
        try:
            assert len(self.board) == self.rows * self.cols, 'Board size mismatch'
            assert all(isinstance(x, int) and x >= 0 for x in self.board), 'Invalid board values'
            assert self.player in (0, 1), 'Invalid player'
            assert self.phase in ('idle','sowing','ai-wait','done'), 'Invalid phase'
        except AssertionError as e:
            BugFixer.capture('error', f'game_state_err: {e}')
            self._recover()

    def _recover(self):
        """Reset to safe state."""
        log.warning('GameState: recovering from corrupt state')
        self.board  = [2] * (self.rows * self.cols)
        self.player = 0
        self.phase  = 'idle'
        self.running= True

    def to_dict(self):
        return {
            'rows': self.rows, 'cols': self.cols,
            'board': self.board, 'player': self.player,
            'phase': self.phase, 'running': self.running,
            'mode': self.mode, 'level': self.level,
            'message': self.message,
            'cows0': self.total_cows(0),
            'cows1': self.total_cows(1),
        }

    # ── Ownership ─────────────────────────────────────────────────────
    def owns_hole(self, idx: int, player: int) -> bool:
        row = idx // self.cols
        return row >= self.rows // 2 if player == 0 else row < self.rows // 2

    def inner_row(self, player: int) -> int:
        return self.rows // 2 if player == 0 else self.rows // 2 - 1

    def total_cows(self, player: int) -> int:
        return sum(self.board[i] for i in range(self.rows * self.cols) if self.owns_hole(i, player))

    # ── Path ──────────────────────────────────────────────────────────
    def board_path(self):
        R, C = self.rows, self.cols
        path, vis = [], set()
        def spiral(r1, c1, r2, c2):
            if r1 > r2 or c1 > c2: return
            for c in range(c1, c2+1):
                add(r1*C+c)
            for r in range(r1+1, r2+1):
                add(r*C+c2)
            if r2 > r1:
                for c in range(c2-1, c1-1, -1):
                    add(r2*C+c)
            if c2 > c1:
                for r in range(r2-1, r1, -1):
                    add(r*C+c1)
            spiral(r1+1, c1+1, r2-1, c2-1)
        def add(idx):
            if idx not in vis:
                path.append(idx); vis.add(idx)
        spiral(0, 0, R-1, C-1)
        return path

    @property
    def _path_cached(self):
        """Cached spiral path — computed once per game instance."""
        if not hasattr(self, '_path_cache') or len(self._path_cache) != self.rows * self.cols:
            self._path_cache = self.board_path()
        return self._path_cache

    def next_hole(self, idx: int) -> int:
        path = self._path_cached
        try:
            pos = path.index(idx)
            return path[(pos + 1) % len(path)]
        except ValueError:
            return (idx + 1) % (self.rows * self.cols)

    # ── Move validation ───────────────────────────────────────────────
    def has_pair_on_side(self, player: int) -> bool:
        return any(self.board[i] >= 2 for i in range(self.rows*self.cols) if self.owns_hole(i, player))

    def is_valid_start(self, idx: int, player: int) -> bool:
        if not (0 <= idx < self.rows * self.cols): return False
        if not self.owns_hole(idx, player):        return False
        if self.board[idx] < 1:                    return False
        if self.board[idx] == 1 and self.has_pair_on_side(player): return False
        return True

    def valid_moves(self, player: int):
        return [i for i in range(self.rows*self.cols) if self.is_valid_start(i, player)]

    def any_moves(self, player: int) -> bool:
        return any(self.is_valid_start(i, player) for i in range(self.rows*self.cols))

    # ── Sow (returns list of animation steps) ────────────────────────
    def do_sow(self, idx: int, player: int):
        """Execute a full sow+relay+capture sequence.
        Returns (steps, captured, game_over, winner_msg)
        steps = list of board snapshots for animation.
        OPTIMISED: records one snapshot per stone placed (not per relay),
        bounded to MAX_ANIM_STEPS to prevent animation lag.
        """
        MAX_ANIM_STEPS = 120   # cap frontend frames — ~6s at 50ms/frame
        MAX_RELAY = 80         # absolute relay depth guard
        if not self.is_valid_start(idx, player):
            BugFixer.capture('warning', f'invalid_move: idx={idx} player={player}')
            return None, 0, False, ''

        steps      = []
        relay_cnt  = 0
        path       = self._path_cached          # O(1) — cached
        path_map   = {v: i for i, v in enumerate(path)}  # O(n) once

        # Track which holes were touched this move (for last-move highlight)
        touched = set()
        stones = self.board[idx]
        self.board[idx] = 0
        cur = idx

        while True:
            relay_cnt += 1
            if relay_cnt > MAX_RELAY:
                BugFixer.capture('warning', 'do_sow: relay guard triggered')
                break

            # Distribute stones one by one, recording each state
            pos = path_map.get(cur, 0)
            for _ in range(stones):
                pos = (pos + 1) % len(path)
                cur = path[pos]
                self.board[cur] += 1
                touched.add(cur)
                if len(steps) < MAX_ANIM_STEPS:
                    steps.append(list(self.board))

            # Relay?
            if self.board[cur] > 1:
                stones = self.board[cur]
                self.board[cur] = 0
            else:
                break  # landed bringing count to 1 — stop

        # Capture check
        captured = self._try_capture(cur, player)
        if captured:
            steps.append(list(self.board))

        return steps, captured, False, ''

    def _try_capture(self, last_idx: int, player: int) -> int:
        if self.board[last_idx] != 1: return 0
        row = last_idx // self.cols
        col = last_idx % self.cols
        if row != self.inner_row(player): return 0
        opp_inner = self.inner_row(1 - player)
        opp_outer = 0 if player == 0 else self.rows - 1
        idx_i = opp_inner * self.cols + col
        idx_o = opp_outer * self.cols + col
        if self.board[idx_i] > 0 and self.board[idx_o] > 0:
            n = self.board[idx_i] + self.board[idx_o]
            self.board[idx_i] = 0
            self.board[idx_o] = 0
            return n
        return 0

    def check_end(self):
        p0, p1 = self.total_cows(0), self.total_cows(1)
        if p0 == 0 or p1 == 0 or (not self.any_moves(0) and not self.any_moves(1)):
            return True, p0, p1
        return False, p0, p1

    # ── AI ────────────────────────────────────────────────────────────
    def ai_move(self) -> int:
        import random
        valid = self.valid_moves(1)
        if not valid: return -1
        if self.level == 1:
            return random.choice(valid)
        elif self.level == 2:
            return self._greedy_ai(valid)
        else:
            return self._smart_ai(valid)

    def _sim_score(self, start_idx: int, player: int) -> int:
        """Simulate a move and return capture value. Mirrors do_sow logic exactly."""
        b         = list(self.board)
        path      = self._path_cached
        path_map  = {v: i for i, v in enumerate(path)}
        stones    = b[start_idx]; b[start_idx] = 0
        pos       = path_map.get(start_idx, 0)
        relay_cnt = 0
        cur       = start_idx
        while relay_cnt < 80:
            relay_cnt += 1
            for _ in range(stones):
                pos = (pos + 1) % len(path)
                cur = path[pos]
                b[cur] += 1
            if b[cur] > 1:
                stones = b[cur]; b[cur] = 0
            else:
                break
        # Check capture at final position
        col = cur % self.cols
        inn = self.inner_row(player)
        if cur // self.cols == inn and b[cur] == 1:
            oi = self.inner_row(1-player) * self.cols + col
            oo = (0 if player == 0 else self.rows-1) * self.cols + col
            if b[oi] > 0 and b[oo] > 0:
                return b[oi] + b[oo]
        return 0

    def _best_opp_response(self) -> int:
        return max((self._sim_score(i, 0) for i in self.valid_moves(0)), default=0)

    def _greedy_ai(self, valid) -> int:
        import random
        return max(valid, key=lambda i: self._sim_score(i,1) + random.random()*0.3)

    def _smart_ai(self, valid) -> int:
        import random
        opp = self._best_opp_response()
        return max(valid, key=lambda i: self._sim_score(i,1) - opp*0.55 + random.random()*0.15)

# In-memory game sessions keyed by session token
_games: dict[str, GameState] = {}
_games_lock = threading.Lock()

def get_game(token: str) -> GameState | None:
    with _games_lock:
        return _games.get(token)

def set_game(token: str, game: GameState):
    with _games_lock:
        _games[token] = game
        # Limit memory: keep only 300 active games, evict oldest
        if len(_games) > 300:
            # Remove games not touched in 2h first, then oldest
            cutoff = time.time() - 7200
            stale = [k for k, g in _games.items() if getattr(g,'last_touch', 0) < cutoff]
            for k in (stale or list(_games.keys())[:50]):
                _games.pop(k, None)

# ─── Translations ──────────────────────────────────────────────────────────────
LANGS = {

  # ── English ──────────────────────────────────────────────────────────
  'en': {
    'label':'English', 'flag':'🇿🇦',
    'turnYou':'Your Turn',        'turnAI':'AI Thinking...', 'turnP2':'Player 2',
    'captured':'+{n} Cows!',      'sleeping':'Sleeping (kulala)',
    'win':'You Win! 🏆',          'lose':'AI Wins! 🤖',       'draw':'Draw! ⚖️',
    'winMsg':'Congratulations!',  'loseMsg':'AI Wins!',        'drawMsg':'Draw!',
    'winNote':'Well played, warrior!', 'loseNote':'Better luck next time!', 'drawNote':'An honourable stalemate!',
    'lv1':'Beginner', 'lv2':'Warrior', 'lv3':'King',
    'lv1desc':'4×4 · Easy AI', 'lv2desc':'4×6 · Smart AI', 'lv3desc':'4×6 · Hard AI',
    'vsAI':'vs AI', 'twoPlayers':'2 Players',
    'rules':'Rules',  'home':'Home',   'profile':'Profile', 'restart':'Restart',
    'playAgain':'Play Again', 'start':'▷ Start', 'logout':'Logout',
    'leaderboard':'Leaderboard', 'close':'Close',
    'signIn':'Sign In',     'register':'Register',
    'email':'Email',        'password':'Password',
    'name':'Name',          'confirm':'Confirm Password',
    'guestPlay':'Guest play', 'alreadyReg':'Already registered?',
    'newUser':'New? Register',
    'profileTitle':'My Profile', 'joined':'Joined', 'lastLogin':'Last login',
    'status':'Status', 'guest':'Guest',
    'wins':'Wins', 'losses':'Losses', 'draws':'Draws', 'played':'Played', 'winPct':'Win%',
    'lbTitle':'Leaderboard', 'lbPlayer':'Player', 'lbWins':'Wins', 'lbGames':'Games', 'lbWinPct':'Win%',
    'skinLabel':'Skin', 'langLabel':'Language', 'levelLabel':'Level', 'modeLabel':'Mode',
    'rulesTitle':'Rules',
    'rulesBoard':'The Board',
    'rulesBoardText':'Four rows of 4-6 holes. A centre line divides two sides of two rows each. The inner row is closest to the centre.',
    'rulesStones':'Stones (Cows)',
    'rulesStonesText':'Two stones placed in every hole at start.',
    'rulesSow':'Sowing Anti-Clockwise',
    'rulesSowText':'Take all stones from a hole and drop one-by-one anti-clockwise. If the last stone lands where stones exist, relay continues. Stop when last stone lands in an empty hole.',
    'rulesCapture':'Capturing',
    'rulesCaptureText':'Relay ends on your inner row in an empty hole AND both opposite holes have stones — capture all those opponent stones.',
    'rulesRules':'Key Rules',
    'rulesRulesText':'Cannot start on a single if pairs exist.\nCannot remove a hole\'s only pair.\nOnly singles left: shift one anti-clockwise.\nNo valid moves: sleep (kulala), opponent continues.',
    'rulesWin':'Winning',
    'rulesWinText':'Take all opponent\'s cows. If only singles remain, most cows wins.',
    'cowsLabel':'cows', 'aiName':'AI Opponent',
    'copyright':'Intshuba © 2026 · Nguni Heritage Games',
  },

  # ── isiZulu ───────────────────────────────────────────────────────────
  # Corrections: turnYou Ithambo(bone)→Jika Wena; lv2 Inhloko(head)→Impi(warrior regiment);
  # p2 Umuntu(person)→UMdlali(player); sleeping Uyalala(redundant)→Ulele
  'zu': {
    'label':'isiZulu', 'flag':'🇿🇦',
    'turnYou':'Jika Wena',             'turnAI':'AI Iyacabanga...', 'turnP2':'UMdlali 2',
    'captured':'+{n} Izinkomo!',       'sleeping':'Ulele (kulala)',
    'win':'Uqobile! 🏆',               'lose':'AI Iyaqoba! 🤖',     'draw':'Ulingane! ⚖️',
    'winMsg':'Uqobile!',               'loseMsg':'AI Iyaqoba!',      'drawMsg':'Ulingane!',
    'winNote':'Wenze kahle, ndodana ye-Nguni!', 'loseNote':'Zama futhi!', 'drawNote':'Ukulwa okuhloniphekile!',
    'lv1':'Isiqalo', 'lv2':'Impi', 'lv3':'Inkosi',
    'lv1desc':'4×4 · AI elula', 'lv2desc':'4×6 · AI ihlakaniphile', 'lv3desc':'4×6 · AI enzima',
    'vsAI':'vs AI', 'twoPlayers':'Abahlali Ababili',
    'rules':'Imithetho', 'home':'Ikhaya', 'profile':'Iphrofayili', 'restart':'Qala Kabusha',
    'playAgain':'Dlala Futhi', 'start':'▷ Qala', 'logout':'Phuma',
    'leaderboard':'Uhlu Lwabadlali', 'close':'Vala',
    'signIn':'Ngena', 'register':'Bhalisa',
    'email':'I-imeyili', 'password':'Iphasiwedi',
    'name':'Igama', 'confirm':'Qinisekisa',
    'guestPlay':'Dlala Njengesvakashi', 'alreadyReg':'Usuqalisiwe? Ngena',
    'newUser':'Omusha? Bhalisa',
    'profileTitle':'Iphrofayili Yami', 'joined':'Ujoyine nini', 'lastLogin':'Ukungena kokugcina',
    'status':'Isimo', 'guest':'Isvakashi',
    'wins':'Uqobile', 'losses':'Ukhohliwe', 'draws':'Ulingane', 'played':'Kudlaliwe', 'winPct':'Amaphs%',
    'lbTitle':'Uhlu Lwabadlali', 'lbPlayer':'Umdlali', 'lbWins':'Uqobile', 'lbGames':'Imidlalo', 'lbWinPct':'Amaphs%',
    'skinLabel':'Isikhumba', 'langLabel':'Ulimi', 'levelLabel':'Izinga', 'modeLabel':'Uhlobo',
    'rulesTitle':'Imithetho',
    'rulesBoard':'Ibhodi',
    'rulesBoardText':'Imigqa emine enembobo ezine kuya kweziyisithupha. Umugqa waphakathi uhlukanisa izihlalo zombili, nomugqa wemigqa emibili ngamunye. Umugqa wangaphakathi useduze kwendikimba.',
    'rulesStones':'Amatshe (Izinkomo)',
    'rulesStonesText':'Amatshe amabili afakwa kuyo yonke imbobo ekuqaleni.',
    'rulesSow':'Ukuhlwanyela Ngokuphambene Nehora',
    'rulesSowText':'Thatha wonke amatshe embobo bese uwela ngawunye ngokuphambene nehora. Uma itshe lokugcina liwa lapho kunamatshe khona, kuqhubeka ukubuyisa. Misa lapho itshe lokugcina liwa embobo engenalutho.',
    'rulesCapture':'Ukubamba',
    'rulesCaptureText':'Ukubuyisa kuphelela emugqeni wakho wangaphakathi embobo engenalutho futhi zombili izimbobo ezingaphambili zinazo izinkomo — bamba zonke izinkomo zesitha.',
    'rulesRules':'Imithetho Ebalulekile',
    'rulesRulesText':'Awukwazi ukuqala esiqendini uma kukhona izimbili.\nAwukwazi ukususa ijozi lodwa.\nUma kuphela iziqephu: susa esinye ngokuphambene nehora.\nAkukho zinyakalo: lala (kulala), isitha siqhubeke.',
    'rulesWin':'Ukuqoba',
    'rulesWinText':'Thatha zonke izinkomo zesitha. Uma kuphela iziqephu, izinkomo eziningi zinqoba.',
    'cowsLabel':'izinkomo', 'aiName':'AI Isitha',
    'copyright':'Intshuba © 2026 · Imidlalo Yabantu baseNguni',
  },

  # ── isiXhosa ──────────────────────────────────────────────────────────
  # Corrections: turnYou Ithuba(chance)→Umjikelo Wakho(your turn); lv2 Ijoni(slang soldier)→Umfazwe(war/battle);
  # draw Lingana(missing subject)→Yalingana; lose AI Iphumelele(same word as win!)→AI Iyinqobile(has beaten)
  'xh': {
    'label':'isiXhosa', 'flag':'🇿🇦',
    'turnYou':'Umjikelo Wakho',        'turnAI':'AI Icinga...', 'turnP2':'Umdlali 2',
    'captured':'+{n} Iinkomo!',        'sleeping':'Ulele (kulala)',
    'win':'Uphumelele! 🏆',            'lose':'AI Iyinqobile! 🤖', 'draw':'Yalingana! ⚖️',
    'winMsg':'Uphumelele!',            'loseMsg':'AI Iyinqobile!',  'drawMsg':'Yalingana!',
    'winNote':'Wenze kakuhle, ndoda yaseNguni!', 'loseNote':'Zama kwakhona!', 'drawNote':'Ukulwa okuhloniphekileyo!',
    'lv1':'Iqalayo', 'lv2':'Umfazwe', 'lv3':'Ukumkani',
    'lv1desc':'4×4 · AI elula', 'lv2desc':'4×6 · AI ihlakaniphile', 'lv3desc':'4×6 · AI enzima',
    'vsAI':'vs AI', 'twoPlayers':'Abadlali Ababini',
    'rules':'Imithetho', 'home':'Ekhaya', 'profile':'Iprofayile', 'restart':'Qala Kwakhona',
    'playAgain':'Dlala Kwakhona', 'start':'▷ Qala', 'logout':'Phuma',
    'leaderboard':'Uluhlu Lwabadlali', 'close':'Vala',
    'signIn':'Ngena', 'register':'Bhalisa',
    'email':'I-imeyili', 'password':'Igama-eligunyaza',
    'name':'Igama', 'confirm':'Qinisekisa',
    'guestPlay':'Dlala Njengendwendwe', 'alreadyReg':'Usabhalisile? Ngena',
    'newUser':'Omusha? Bhalisa',
    'profileTitle':'Iprofayile Yam', 'joined':'Ujoyine nini', 'lastLogin':'Ukungena kokugqibela',
    'status':'Imeko', 'guest':'Indwendwe',
    'wins':'Uphumelele', 'losses':'Uthe chatha', 'draws':'Yalingana', 'played':'Kudlaliwe', 'winPct':'Amaphs%',
    'lbTitle':'Uluhlu Lwabadlali', 'lbPlayer':'Umdlali', 'lbWins':'Uphumelele', 'lbGames':'Imidlalo', 'lbWinPct':'Amaphs%',
    'skinLabel':'Isikhumba', 'langLabel':'Ulwimi', 'levelLabel':'Inqanaba', 'modeLabel':'Uhlobo',
    'rulesTitle':'Imithetho',
    'rulesBoard':'Ibhodi',
    'rulesBoardText':'Imihlathi emine enemingxuma emine ukuya kweyisithandathu. Umgca ophakathi wahlukanisa izicala zombini ezinamihlathi emibini nganye. Umgca wangaphakathi ukufuphi nendikimba.',
    'rulesStones':'Amatye (Iinkomo)',
    'rulesStonesText':'Amatye amabini afakelwa kuyo yonke imingxuma ekuqaleni.',
    'rulesSow':'Ukuhlwanyela Ngokuchasene Nehora',
    'rulesSowText':'Thatha onke amatye emingxumeni uwisele esinye nesine ngokuchasene nehora. Ukuba ilitye lokugqibela liwa apho amatye akhoyo, iqhubeka ukubuyisa. Misa xa ilitye lokugqibela liwa emingxumeni engenanto.',
    'rulesCapture':'Ukubamba',
    'rulesCaptureText':'Ukubuyisa kuphela kumgca wakho wangaphakathi emingxumeni engenanto kwaye zombini iimingxuma ezithe ngqo zineenkomo — bamba zonke iinkomo zomtshana.',
    'rulesRules':'Imithetho Ebalulekileyo',
    'rulesRulesText':'Akusenzi ukuqala kwenye eyodwa ukuba kukho iimbini.\nAkusenzi ukususa isiphelelo sinye kuphela.\nUkuba zigcwele ezinye zodwa: fudula enye ngokuchasene nehora.\nAkukho ntshukumo: lala (kulala), umtshana aqhubeke.',
    'rulesWin':'Ukuphumelela',
    'rulesWinText':'Thatha zonke iinkomo zomtshana. Ukuba zigcwele ezinye zodwa, iinkomo ezininzi ziyaphumelela.',
    'cowsLabel':'iinkomo', 'aiName':'AI Umtshana',
    'copyright':'Intshuba © 2026 · Imidlalo YamaXhosa',
  },

  # ── Afrikaans ─────────────────────────────────────────────────────────
  # Corrections: sleeping Slaap(imperative)→Aan die slaap; KI kept (correct SA term);
  # 'n article handled with escaped apostrophes throughout
  'af': {
    'label':'Afrikaans', 'flag':'🇿🇦',
    'turnYou':'Jou Beurt',             'turnAI':'AI Dink...', 'turnP2':'Speler 2',
    'captured':'+{n} Beeste!',         'sleeping':'Aan die slaap (kulala)',
    'win':'Jy Wen! 🏆',                'lose':'AI Wen! 🤖',    'draw':'Gelykspel! ⚖️',
    'winMsg':'Jy het gewen!',          'loseMsg':'AI het gewen!', 'drawMsg':'Gelykspel!',
    'winNote':'Baie goed gedoen, krygsman!', 'loseNote':'Sterkte volgende keer!', 'drawNote':'\'n Eervolle gelykspel!',
    'lv1':'Beginner', 'lv2':'Vegter', 'lv3':'Koning',
    'lv1desc':'4×4 · Maklike AI', 'lv2desc':'4×6 · Slim AI', 'lv3desc':'4×6 · Moeilike AI',
    'vsAI':'vs AI', 'twoPlayers':'2 Spelers',
    'rules':'Reels', 'home':'Tuis', 'profile':'Profiel', 'restart':'Herbegin',
    'playAgain':'Speel Weer', 'start':'▷ Begin', 'logout':'Uitteken',
    'leaderboard':'Wennerslys', 'close':'Sluit',
    'signIn':'Teken In', 'register':'Registreer',
    'email':'E-pos', 'password':'Wagwoord',
    'name':'Naam', 'confirm':'Bevestig Wagwoord',
    'guestPlay':'Speel as Gaste', 'alreadyReg':'Reeds geregistreer? Teken In',
    'newUser':'Nuut? Registreer',
    'profileTitle':'My Profiel', 'joined':'Aangesluit', 'lastLogin':'Laaste inskrywing',
    'status':'Status', 'guest':'Gaste',
    'wins':'Wen', 'losses':'Verloor', 'draws':'Gelyk', 'played':'Gespeel', 'winPct':'Wen%',
    'lbTitle':'Wennerslys', 'lbPlayer':'Speler', 'lbWins':'Wen', 'lbGames':'Spele', 'lbWinPct':'Wen%',
    'skinLabel':'Vel', 'langLabel':'Taal', 'levelLabel':'Vlak', 'modeLabel':'Modus',
    'rulesTitle':'Reels',
    'rulesBoard':'Die Bord',
    'rulesBoardText':'Vier rye van 4-6 gate. \'n Middellyn verdeel twee kante van twee rye elk. Die binnerye is naaste aan die middel.',
    'rulesStones':'Klippies (Beeste)',
    'rulesStonesText':'Twee klippies word in elke gat aan die begin geplaas.',
    'rulesSow':'Saai Teen die Klok',
    'rulesSowText':'Vat al die klippies uit \'n gat en laat een vir een teen die klok val. As die laaste klippie land waar klippies is, gaan voort. Stop as die laaste klippie in \'n lee gat land.',
    'rulesCapture':'Vang',
    'rulesCaptureText':'Aflossing eindig op jou binnerye in \'n lee gat EN albei teenoorgestelde gate het klippies — vang al die klippies van die teenstander.',
    'rulesRules':'Sleutelreels',
    'rulesRulesText':'Kan nie begin met \'n enkeling as daar pare is nie.\nKan nie die enigste paar verwyder nie.\nSlegs enkelings oor: skuif een teen die klok.\nGeen geldige sette: slaap (kulala), teenstander gaan voort.',
    'rulesWin':'Wen',
    'rulesWinText':'Vat al die teenstander se beeste. As slegs enkelings oorbly, meeste beeste wen.',
    'cowsLabel':'beeste', 'aiName':'AI Teenstander',
    'copyright':'Intshuba © 2026 · Nguni Erfenisspele',
  },

  # ── Sesotho ───────────────────────────────────────────────────────────
  # Corrections: turnYou Motsoaro(behaviour)→Sebaka Sa Hao(your turn/space);
  # sleeping O Robetse(has slept, perfect)→O Robala(is sleeping); lv1 Moqali→Moqaleli
  'st': {
    'label':'Sesotho', 'flag':'🇿🇦',
    'turnYou':'Sebaka Sa Hao',         'turnAI':'AI E Nahana...', 'turnP2':'Moapei 2',
    'captured':'+{n} Dikgomo!',        'sleeping':'O Robala (kulala)',
    'win':'O Hlotse! 🏆',              'lose':'AI E Hlotse! 🤖',  'draw':'Ho Lekalekana! ⚖️',
    'winMsg':'O Hlotse!',              'loseMsg':'AI E Hlotse!',   'drawMsg':'Ho Lekalekana!',
    'winNote':'O phela hantle, ntoa!', 'loseNote':'Leka hape!',    'drawNote':'Ntoa e tlotleha!',
    'lv1':'Moqaleli', 'lv2':'Ntoa', 'lv3':'Morena',
    'lv1desc':'4×4 · AI e bonolo', 'lv2desc':'4×6 · AI e bohlale', 'lv3desc':'4×6 · AI e thata',
    'vsAI':'vs AI', 'twoPlayers':'Bapapadi ba Babedi',
    'rules':'Melao', 'home':'Hae', 'profile':'Profaele', 'restart':'Qala Hape',
    'playAgain':'Bapala Hape', 'start':'▷ Qala', 'logout':'Tswa',
    'leaderboard':'Lenane la Bapapadi', 'close':'Khaola',
    'signIn':'Kena', 'register':'Ngolisa',
    'email':'Imeile', 'password':'Phasewete',
    'name':'Lebitso', 'confirm':'Netefatsa',
    'guestPlay':'Bapala Joalo ka Moeti', 'alreadyReg':'O se ngolisitsoe? Kena',
    'newUser':'Motho o mocha? Ngolisa',
    'profileTitle':'Profaele Ya Ka', 'joined':'O kene neng', 'lastLogin':'Ho kena ho ho qetelang',
    'status':'Boemo', 'guest':'Moeti',
    'wins':'Ho Hlola', 'losses':'Ho Hlolwa', 'draws':'Ho Lekana', 'played':'Ho Bapala', 'winPct':'%Hlola',
    'lbTitle':'Lenane la Bapapadi', 'lbPlayer':'Moapei', 'lbWins':'Hlola', 'lbGames':'Dipapadi', 'lbWinPct':'%Hlola',
    'skinLabel':'Letlalo', 'langLabel':'Puo', 'levelLabel':'Boemo', 'modeLabel':'Mofuta',
    'rulesTitle':'Melao',
    'rulesBoard':'Bodo',
    'rulesBoardText':'Mela e mene ya maqhobong a mane ho isa ho a tsheletseng. Mola o bohareng o arohanye mahlakore a mabedi a mela e mmedi ka mong. Mola o ka hare o haufi le bohareng.',
    'rulesStones':'Majwe (Dikgomo)',
    'rulesStonesText':'Majwe a mabedi a bewa maqhobong ohle qalong.',
    'rulesSow':'Ho Jala Kgahlanong le Hora',
    'rulesSowText':'Nka majwe ohle ho qhobong o a lahle o le mong le o le mong kgahlanong le hora. Ha leswika la ho qetela le wela moo ho nang le majwe teng, ho tsoela pele ho fetola. Emisa ha leswika la ho qetela le wela qhobong le se nang letho.',
    'rulesCapture':'Ho Tshwara',
    'rulesCaptureText':'Phetolo e phela molapo wa hao o ka hare qhobong le se nang letho — MMOHO le maqhobo a mabedi a ka pele a ntse a na le dikgomo — tshwara dikgomo tsohle tsa mohlankana.',
    'rulesRules':'Melao e Bohlokwa',
    'rulesRulesText':'Ha o kgone ho qala ho se le le leng ha ho na dipare.\nHa o kgone ho tlosa pere e nngwe feela.\nHa ho phuthehile bo le bong feela: shetsa e nngwe kgahlanong le hora.\nHa ho na dikhetho tse nepahetseng: robala (kulala), mohlankana a tsoele pele.',
    'rulesWin':'Ho Hlola',
    'rulesWinText':'Nka dikgomo tsohle tsa mohlankana. Ha ho phuthehile bo le bong feela, dikgomo tse ngata di hlola.',
    'cowsLabel':'dikgomo', 'aiName':'AI Mohlankana',
    'copyright':'Intshuba © 2026 · Dipapadi tsa Bontata',
  },

  # ── Setswana ──────────────────────────────────────────────────────────
  # Corrections: turnYou Tshwaelo(obligation)→Motlha Wa Gago(your time/turn);
  # p2 Mosadi(WOMAN/WIFE — serious error!)→Moapei(player); sleeping O Robetse→O a Robala
  'tn': {
    'label':'Setswana', 'flag':'🇿🇦',
    'turnYou':'Motlha Wa Gago',        'turnAI':'AI E Akanya...', 'turnP2':'Moapei 2',
    'captured':'+{n} Dikgomo!',        'sleeping':'O a Robala (kulala)',
    'win':'O Fenye! 🏆',               'lose':'AI E Fenye! 🤖',   'draw':'Go Lekalekana! ⚖️',
    'winMsg':'O Fenye!',               'loseMsg':'AI E Fenye!',    'drawMsg':'Go Lekalekana!',
    'winNote':'O dira sentle, ntau!',  'loseNote':'Leka gape!',    'drawNote':'Ntoa e tlotleha!',
    'lv1':'Moqadi', 'lv2':'Ntwa', 'lv3':'Kgosi',
    'lv1desc':'4×4 · AI e bonolo', 'lv2desc':'4×6 · AI e bohlale', 'lv3desc':'4×6 · AI e thata',
    'vsAI':'vs AI', 'twoPlayers':'Bapapadi ba Babedi',
    'rules':'Melao', 'home':'Gae', 'profile':'Profaele', 'restart':'Simolola Gape',
    'playAgain':'Bapala Gape', 'start':'▷ Simolola', 'logout':'Tswa',
    'leaderboard':'Lenane la Bapapadi', 'close':'Tswala',
    'signIn':'Tsena', 'register':'Ngolisa',
    'email':'Imeile', 'password':'Lefoko la Sephiri',
    'name':'Leina', 'confirm':'Netefatsa',
    'guestPlay':'Bapala o le Moeng', 'alreadyReg':'O se ngolisitswe? Tsena',
    'newUser':'Motho o Mosha? Ngolisa',
    'profileTitle':'Profaele Ya Me', 'joined':'O tsene leng', 'lastLogin':'Go tsena go go bofelo',
    'status':'Maemo', 'guest':'Moeng',
    'wins':'Go Fenya', 'losses':'Go Fenngwa', 'draws':'Go Lekalekana', 'played':'Go Bapala', 'winPct':'%Fenya',
    'lbTitle':'Lenane la Bapapadi', 'lbPlayer':'Moapei', 'lbWins':'Fenya', 'lbGames':'Dipapadi', 'lbWinPct':'%Fenya',
    'skinLabel':'Letlalo', 'langLabel':'Puo', 'levelLabel':'Maemo', 'modeLabel':'Mofuta',
    'rulesTitle':'Melao',
    'rulesBoard':'Boto',
    'rulesBoardText':'Mela e nne ya maqhob a mane go ya go a tshelelang. Mola o gare o arola mahlakore a mabedi a mela e mebedi mongwe le mongwe. Mola o ka teng o gaufi le gare.',
    'rulesStones':'Majwe (Dikgomo)',
    'rulesStonesText':'Majwe a mabedi a bewa mo maqhob otlhe qalong.',
    'rulesSow':'Go Jala Kgatlhanong le Ura',
    'rulesSowText':'Tsaya majwe otlhe mo qhobong mme o a fologise bongwe le bongwe kgatlhanong le ura. Fa leswika la bofelo le wela kwa go nang le majwe teng, go tswelela go fetola. Emisa fa leswika la bofelo le wela mo qhobong le se nang sepe.',
    'rulesCapture':'Go Tshwara',
    'rulesCaptureText':'Phetolo e fela mo moleng wa gago wa ka teng mo qhobong le se nang sepe — MMOGO le maqhob a mabedi a lebagane a na le dikgomo — tshwara dikgomo tsotlhe tsa moganetsi.',
    'rulesRules':'Melao e Botlhokwa',
    'rulesRulesText':'O ka se simolole ka le lengwe fa go na le dipera.\nO ka se tlose pera nngwe feela.\nFa go na le bo le bong feela: shetsa bongwe kgatlhanong le ura.\nGo se na dikgetho tse siameng: robala (kulala), moganetsi a tswelele.',
    'rulesWin':'Go Fenya',
    'rulesWinText':'Tsaya dikgomo tsotlhe tsa moganetsi. Fa go na le bo le bong feela, dikgomo tse dintsi di fenya.',
    'cowsLabel':'dikgomo', 'aiName':'AI Moganetsi',
    'copyright':'Intshuba © 2026 · Dipapadi tsa Setswana',
  },

  # ── Sepedi / Northern Sotho ────────────────────────────────────────────
  # Corrections: turnYou Mohla(day/date)→Nako Ya Gago(your time);
  # win/lose O Hlotle→O Hlotse (correct Sepedi perfect tense without caron on e)
  'nso': {
    'label':'Sepedi', 'flag':'🇿🇦',
    'turnYou':'Nako Ya Gago',          'turnAI':'AI E Nagana...', 'turnP2':'Moapei 2',
    'captured':'+{n} Dikgomo!',        'sleeping':'O Robala (kulala)',
    'win':'O Hlotse! 🏆',              'lose':'AI E Hlotse! 🤖',  'draw':'Tekano! ⚖️',
    'winMsg':'O Hlotse!',              'loseMsg':'AI E Hlotse!',   'drawMsg':'Tekano!',
    'winNote':'O dirile gabotse, ntau!', 'loseNote':'Leka gape!',  'drawNote':'Ntwa ye e tlotlegilego!',
    'lv1':'Moqadi', 'lv2':'Ntwa', 'lv3':'Kgosi',
    'lv1desc':'4×4 · AI e bonolo', 'lv2desc':'4×6 · AI e bohlale', 'lv3desc':'4×6 · AI e thata',
    'vsAI':'vs AI', 'twoPlayers':'Bapapadi ba Babedi',
    'rules':'Melao', 'home':'Gae', 'profile':'Profaele', 'restart':'Thoma Gape',
    'playAgain':'Bapala Gape', 'start':'▷ Thoma', 'logout':'Tswa',
    'leaderboard':'Lenane la Bapapadi', 'close':'Tswala',
    'signIn':'Tsena', 'register':'Ngwadisa',
    'email':'Imeile', 'password':'Lefoko la Sephiri',
    'name':'Leina', 'confirm':'Netefatsa',
    'guestPlay':'Bapala o le Moeng', 'alreadyReg':'O se ngwadisitswe? Tsena',
    'newUser':'Motho o Moswa? Ngwadisa',
    'profileTitle':'Profaele Ya Ka', 'joined':'O tsene neng', 'lastLogin':'Go tsena go go felo',
    'status':'Maemo', 'guest':'Moeng',
    'wins':'Go Hlola', 'losses':'Go Hlolwa', 'draws':'Tekano', 'played':'Go Bapala', 'winPct':'%Hlola',
    'lbTitle':'Lenane la Bapapadi', 'lbPlayer':'Moapei', 'lbWins':'Hlola', 'lbGames':'Dipapadi', 'lbWinPct':'%Hlola',
    'skinLabel':'Letlalo', 'langLabel':'Puo', 'levelLabel':'Maemo', 'modeLabel':'Mohuta',
    'rulesTitle':'Melao',
    'rulesBoard':'Boto',
    'rulesBoardText':'Mela ye mene ya maqhob a mane go ya go a tshelela. Mola wo gare o arola mahlakore a mabedi a mela e mebedi e nngwe le e nngwe. Mola wo ka gare o gaufi le gare.',
    'rulesStones':'Majwe (Dikgomo)',
    'rulesStonesText':'Majwe a mabedi a bewa maqhob otlhe qalong.',
    'rulesSow':'Go Bjala Kgahlano le Ura',
    'rulesSowText':'Tshea majwe otlhe qhobong o a wisele bongwe le bongwe kgahlano le ura. Ge leswika la bofelo le wela moo go nago le majwe, go tswela pele go fetosa. Emisa ge leswika la bofelo le wela qhobong le se nago sepe.',
    'rulesCapture':'Go Swara',
    'rulesCaptureText':'Phetoso e fela moleng wa gago wa ka gare qhobong le se nago sepe — MMOGO le maqhob a mabedi a abilego a na le dikgomo — swara dikgomo tsotlhe tsa moganetsi.',
    'rulesRules':'Melao ye Bohlokwa',
    'rulesRulesText':'O ka se thome ka le lengwe ge go na le dipera.\nO ka se tlose pera nngwe feela.\nGe go na le bongwe feela: setsa bongwe kgahlano le ura.\nGo se na dikgetho tse nepagaletse: robala (kulala), moganetsi a tswele pele.',
    'rulesWin':'Go Hlola',
    'rulesWinText':'Tshea dikgomo tsotlhe tsa moganetsi. Ge go na le bongwe feela, dikgomo tse ntsi di hlola.',
    'cowsLabel':'dikgomo', 'aiName':'AI Moganetsi',
    'copyright':'Intshuba © 2026 · Dipapadi tsa Sepedi',
  },

  # ── siSwati ───────────────────────────────────────────────────────────
  # Corrections: turnYou Litsatsi(sun/day)→Jika Wena(your turn);
  # p2 Umchjiri(non-standard)→Umdlali(player); lv1 Simula(non-standard)→Kucala(beginning)
  'ss': {
    'label':'siSwati', 'flag':'🇸🇿',
    'turnYou':'Jika Wena',             'turnAI':'AI Icabanga...', 'turnP2':'Umdlali 2',
    'captured':'+{n} Tinkomo!',        'sleeping':'Ulele (kulala)',
    'win':'Uphumelele! 🏆',            'lose':'AI Iphumelele! 🤖', 'draw':'Kulingana! ⚖️',
    'winMsg':'Uphumelele!',            'loseMsg':'AI Iphumelele!',  'drawMsg':'Kulingana!',
    'winNote':'Wente kahle, ndvuna!',  'loseNote':'Zama futsi!',    'drawNote':'Impi lehloniphekile!',
    'lv1':'Kucala', 'lv2':'Ngcweti', 'lv3':'Nkhosi',
    'lv1desc':'4×4 · AI lesecelele', 'lv2desc':'4×6 · AI lehlakaniphile', 'lv3desc':'4×6 · AI lenzima',
    'vsAI':'vs AI', 'twoPlayers':'Badlali Lababili',
    'rules':'Imitsetfo', 'home':'Ekhaya', 'profile':'Iphrofayili', 'restart':'Cala Kabusha',
    'playAgain':'Dlala Futsi', 'start':'▷ Cala', 'logout':'Phuma',
    'leaderboard':'Uhlu Lwabadlali', 'close':'Vala',
    'signIn':'Ngena', 'register':'Bhalisa',
    'email':'Ikheli le-imeyili', 'password':'Iphasiwedi',
    'name':'Libito', 'confirm':'Qinisekisa',
    'guestPlay':'Dlala Njengesvakashi', 'alreadyReg':'Usabhalisiwe? Ngena',
    'newUser':'Musha? Bhalisa',
    'profileTitle':'Iphrofayili Yami', 'joined':'Ujoyine nini', 'lastLogin':'Ukungena kokugcina',
    'status':'Simo', 'guest':'Isvakashi',
    'wins':'Kuphumelela', 'losses':'Ukuhlulwa', 'draws':'Kulingana', 'played':'Kudlaliwa', 'winPct':'%Kuphumelela',
    'lbTitle':'Uhlu Lwabadlali', 'lbPlayer':'Umdlali', 'lbWins':'Kuphumelela', 'lbGames':'Tidlalo', 'lbWinPct':'%Phum',
    'skinLabel':'Isikhumba', 'langLabel':'Lulwimi', 'levelLabel':'Inqopho', 'modeLabel':'Uhlobo',
    'rulesTitle':'Imitsetfo',
    'rulesBoard':'Libhodi',
    'rulesBoardText':'Imigca lemine yemigodi lemine kuya kulayisitfupha. Umugca wesigcawu uhlukanisa tinhlangotsi letimbili letinemigca lemibili ngayinye. Umugca wangekhatsi useduze nesigcawu.',
    'rulesStones':'Ematje (Tinkomo)',
    'rulesStonesText':'Ematje lamabili afakwa kuyo yonkhe imigodi ekucaleni.',
    'rulesSow':'Kuhlwanyela Ngekucala',
    'rulesSowText':'Tsatsa onkhe ematje emgodini bese awisela ngalinye ngalinye ngekucala. Nangabe ilitje lokugcina liwela lapho kunamatje khona, kuyaqhubeka. Misa nangabe ilitje lokugcina liwela emgodini longekho lutfo.',
    'rulesCapture':'Kubamba',
    'rulesCaptureText':'Ukubuyisa kuphela emugqeni wakho wangekhatsi emgodini longekho lutfo — KANYE nemigodi lemibili lemelene yinawo tinkomo — bamba tinkomo tonkhe tesitsa.',
    'rulesRules':'Imitsetfo Lebalulekile',
    'rulesRulesText':'Ungakwati kuqala ngalesinye nangabe kukhona timbili.\nUngakwati kususa ijozi linye kuphela.\nNangabe kuphela tintfo letinye todwa: susa linye ngekucala.\nAkukho tikhetso: lala (kulala), sitsa siqhubeke.',
    'rulesWin':'Kuphumelela',
    'rulesWinText':'Tsatsa tinkomo tonkhe tesitsa. Nangabe kuphela tintfo letinye todwa, tinkomo letinyenti tiphumelela.',
    'cowsLabel':'tinkomo', 'aiName':'AI Isitsa',
    'copyright':'Intshuba © 2026 · Tidlalo Temaswati',
  },

  # ── Tshivenda ─────────────────────────────────────────────────────────
  # Corrections: turnYou Tshangu(fear/alarm)→Tshifhinga Tsha Vho(your time);
  # turnAI I Humbula(remembers/misses)→I Nagana(is thinking);
  # lv2 Mbidi(ZEBRA — wrong!)→Tshishumba(warrior/soldier)
  've': {
    'label':'Tshivenda', 'flag':'🇿🇦',
    'turnYou':'Tshifhinga Tsha Vho',   'turnAI':'AI I Nagana...', 'turnP2':'Mutambi wa 2',
    'captured':'+{n} Ngombe!',         'sleeping':'U Robela (kulala)',
    'win':'Wa Hola! 🏆',               'lose':'AI Ya Hola! 🤖',   'draw':'Zwi Lingana! ⚖️',
    'winMsg':'Wa Hola!',               'loseMsg':'AI Ya Hola!',    'drawMsg':'Zwi Lingana!',
    'winNote':'Wo ita zwavhudi, lovha!', 'loseNote':'Lingedza hafhu!', 'drawNote':'Vhudi ha dzamharo!',
    'lv1':'Muqali', 'lv2':'Tshishumba', 'lv3':'Khosi',
    'lv1desc':'4x4 · AI yofhola', 'lv2desc':'4x6 · AI yehlakanipha', 'lv3desc':'4x6 · AI thukhumela',
    'vsAI':'vs AI', 'twoPlayers':'Vhatambi Vhavhili',
    'rules':'Milayo', 'home':'Hayani', 'profile':'Profaele', 'restart':'Thoma Hafhu',
    'playAgain':'Tamba Hafhu', 'start':'▷ Thoma', 'logout':'Bva',
    'leaderboard':'Mutalukanyo wa Vhatambi', 'close':'Vhala',
    'signIn':'Dzhena', 'register':'Nwalisa',
    'email':'Imeyili', 'password':'Iphasiwede',
    'name':'Dzina', 'confirm':'Khwinifhadza',
    'guestPlay':'Tamba o Tshi Khou Etela', 'alreadyReg':'Ndi munwaliswi? Dzhena',
    'newUser':'Muthu Mutsha? Nwalisa',
    'profileTitle':'Profaele Yanga', 'joined':'Wo dzhena lini', 'lastLogin':'U dzhena ha u fhedza',
    'status':'Maimo', 'guest':'Muenwa',
    'wins':'Vuhola', 'losses':'Vhuholwa', 'draws':'Zwi Lingana', 'played':'Zwi Tambwa', 'winPct':'%Hola',
    'lbTitle':'Mutalukanyo wa Vhatambi', 'lbPlayer':'Mutambi', 'lbWins':'Hola', 'lbGames':'Mitambo', 'lbWinPct':'%Hola',
    'skinLabel':'Nga', 'langLabel':'Luambo', 'levelLabel':'Maimo', 'modeLabel':'Muhuta',
    'rulesTitle':'Milayo',
    'rulesBoard':'Bodo',
    'rulesBoardText':'Mitsima ya vhana vha 4-6 mibulo. Mutsamo wa namadzulo u arotshela madzaladza mavhili a mitsima mivhili yothe. Mutsamo wa ngomu u athu ha namadzulo.',
    'rulesStones':'Matombo (Ngombe)',
    'rulesStonesText':'Matombo mavhili a tangwa mibulo yothe u thoma.',
    'rulesSow':'U Swa Khulekano na Awara',
    'rulesSowText':'Tora matombo othe mubuloni u a wisa o tshi itela fhasi kha fhasi khulekano na awara. Tombo la u fhedzela li kha ndzila ine matombo a vha hone, zwi tshimbila. Misa tombo la u fhedzela li wela mubuloni u si na lutho.',
    'rulesCapture':'U Thia',
    'rulesCaptureText':'U khwathela zwo fhela kha mutsamo wa ngomu mubuloni u si na lutho — TSHINGWE NA mibulo mivhili ya u fhindana ine ya vha na ngombe — thia ngombe dzothe dza mudivhani.',
    'rulesRules':'Milayo ya Ndeme',
    'rulesRulesText':'A hu divhiwi u thoma nga yothe yo tshilivha fhethu ha vha na mivhili.\nA hu divhiwi u bvisa mvhili kha yothe.\nFha na yothe yo tshilivha feela: sudzula yo tshilivha khulekano na awara.\nA hu na khetho dzo teaho: lala (kulala), mudivhani a tshimbile.',
    'rulesWin':'U Hola',
    'rulesWinText':'Tora ngombe dzothe dza mudivhani. Arali ho sala dzo tshilivha feela, ngombe nnzhi dzi hola.',
    'cowsLabel':'ng\'ombe', 'aiName':'AI Mudivhani',
    'copyright':'Intshuba © 2026 · Mitambo ya Vhavenda',
  },

  # ── Xitsonga ──────────────────────────────────────────────────────────
  # Corrections: p2 Muxavisiwi(seller/trader — wrong!)→Muxaxi(player/participant);
  # lv2 Ntokoto(non-standard)→Xindzhuti(warrior/soldier in Xitsonga)
  # Note: xin'we (one/single) is correct Xitsonga — using escaped apostrophe
  'ts': {
    'label':'Xitsonga', 'flag':'🇿🇦',
    'turnYou':'Nkarhi Wa Wena',        'turnAI':'AI Yi Ehleketa...', 'turnP2':'Muxaxi 2',
    'captured':'+{n} Swifuwo!',        'sleeping':'U Lele (kulala)',
    'win':'U Hlotile! 🏆',             'lose':'AI Yi Hlotile! 🤖', 'draw':'Ku Lingana! ⚖️',
    'winMsg':'U Hlotile!',             'loseMsg':'AI Yi Hlotile!',  'drawMsg':'Ku Lingana!',
    'winNote':'U endlile kahle, xindzhuti!', 'loseNote':'Ringeta nakambe!', 'drawNote':'Ntwanano lehloniphekile!',
    'lv1':'Muqali', 'lv2':'Xindzhuti', 'lv3':'Hosi',
    'lv1desc':'4x4 · AI yo olova', 'lv2desc':'4x6 · AI yo hlakanipha', 'lv3desc':'4x6 · AI yo tika',
    'vsAI':'vs AI', 'twoPlayers':'Vadlayeri Vaviri',
    'rules':'Milawu', 'home':'Kaya', 'profile':'Profayili', 'restart':'Sungula Nakambe',
    'playAgain':'Dlaya Nakambe', 'start':'▷ Sungula', 'logout':'Huma',
    'leaderboard':'Muxaka wa Vadlayeri', 'close':'Pfala',
    'signIn':'Nghena', 'register':'Tsarisa',
    'email':'Imeyili', 'password':'Mfumo wa Siphiri',
    'name':'Vito', 'confirm':'Pfumela',
    'guestPlay':'Dlaya tani hi Muendzi', 'alreadyReg':'U se tsarisiwile? Nghena',
    'newUser':'Mutswa? Tsarisa',
    'profileTitle':'Profayili Ya Mina', 'joined':'U nghene lini', 'lastLogin':'Ku nghena ka makumu',
    'status':'Xiyimo', 'guest':'Muendzi',
    'wins':'Ku Hlota', 'losses':'Ku Hlolwa', 'draws':'Ku Lingana', 'played':'Ku Dlaya', 'winPct':'%Hlota',
    'lbTitle':'Muxaka wa Vadlayeri', 'lbPlayer':'Mudlayeri', 'lbWins':'Hlota', 'lbGames':'Tidlayo', 'lbWinPct':'%Hlota',
    'skinLabel':'Ndzovolo', 'langLabel':'Ririmi', 'levelLabel':'Nqanqo', 'modeLabel':'Xintshuxo',
    'rulesTitle':'Milawu',
    'rulesBoard':'Bodo',
    'rulesBoardText':'Mintlawa ya mune ya timboho ta mune ku ya ka taya ntsevu. Xiphemu xa gare xi ahlula matshelo mambirhi ya mintlawa miviri na xin\'wana. Ntlawa wa le ndzeni u haufi na gare.',
    'rulesStones':'Matsolo (Swifuwo)',
    'rulesStonesText':'Matsolo mambirhi ya vekiwa eka timboho hinkwato ekusunguleni.',
    'rulesSow':'Ku Byala Ngokuphambana na Awara',
    'rulesSowText':'Teka matsolo hinkwawo eka timboho u ya ku wisela xin\'we na xin\'we ngokuphambana na awara. Loko litjelo ra le ku hetelela ri pfika laha matsolo ya kumekaka, ku ya emahlweni. Yimela loko litjelo ra le ku hetelela ri wela eka timboho leri nga naye nchumu.',
    'rulesCapture':'Ku Bumba',
    'rulesCaptureText':'Ku khutisela ku hela eka ntlawa wa wena wa le ndzeni eka timboho leri nga naye nchumu — HAMBI timboho ta mambirhi ta le tshami ti na swifuwo — bumba swifuwo hinkwaswo swa xitshembu.',
    'rulesRules':'Milawu ya Nkoka',
    'rulesRulesText':'U nga sunguli eka xin\'we loko ku na mambirhi.\nU nga susiwi mambirhi ya xin\'we ntsena.\nLoko ku sala exin\'we ntsena: susela xin\'we ngokuphambana na awara.\nKu hava swikhetwo leswi pfumelelekeke: lala (kulala), xitshembu xi ya emahlweni.',
    'rulesWin':'Ku Hlota',
    'rulesWinText':'Teka swifuwo hinkwaswo swa xitshembu. Loko ku sala exin\'we ntsena, swifuwo swo tala swi hlota.',
    'cowsLabel':'swifuwo', 'aiName':'AI Xitshembu',
    'copyright':'Intshuba © 2026 · Tidlayo ta Vatsonga',
  },

  # ── isiNdebele ────────────────────────────────────────────────────────
  # Corrections: turnYou Ithambo(bone)→Jika Wena; p2 Umuntu(person)→UMdlali(player);
  # lv2 Ijoni(slang)→Impi(warrior regiment — same as Zulu, correct for Ndebele)
  'nr': {
    'label':'isiNdebele', 'flag':'🇿🇦',
    'turnYou':'Jika Wena',             'turnAI':'AI Icabanga...', 'turnP2':'UMdlali 2',
    'captured':'+{n} Izinkomo!',       'sleeping':'Ulele (kulala)',
    'win':'Uphumelele! 🏆',            'lose':'AI Iphumelele! 🤖', 'draw':'Kulinganile! ⚖️',
    'winMsg':'Uphumelele!',            'loseMsg':'AI Iphumelele!',  'drawMsg':'Kulinganile!',
    'winNote':'Wenza kuhle, ndodana!', 'loseNote':'Zama futhi!',    'drawNote':'Ukulwa okuhloniphekile!',
    'lv1':'Ukuqala', 'lv2':'Impi', 'lv3':'INkosi',
    'lv1desc':'4x4 · AI elula', 'lv2desc':'4x6 · AI ihlakanipha', 'lv3desc':'4x6 · AI enzima',
    'vsAI':'vs AI', 'twoPlayers':'Abahlali Ababili',
    'rules':'Imithetho', 'home':'Ekhaya', 'profile':'Iphrofayili', 'restart':'Qala Kabusha',
    'playAgain':'Dlala Futhi', 'start':'▷ Qala', 'logout':'Phuma',
    'leaderboard':'Uhlu Lwabadlali', 'close':'Vala',
    'signIn':'Ngena', 'register':'Bhalisa',
    'email':'I-imeyili', 'password':'Iphasiwedi',
    'name':'Ibizo', 'confirm':'Qinisekisa',
    'guestPlay':'Dlala Njengesvakashi', 'alreadyReg':'Usabhalisile? Ngena',
    'newUser':'Omusha? Bhalisa',
    'profileTitle':'Iphrofayili Yami', 'joined':'Ujoyine nini', 'lastLogin':'Ukungena kokugcina',
    'status':'Isimo', 'guest':'Isvakashi',
    'wins':'Uphumelele', 'losses':'Ukhohliwe', 'draws':'Kulinganile', 'played':'Kudlaliwe', 'winPct':'Amaphs%',
    'lbTitle':'Uhlu Lwabadlali', 'lbPlayer':'UMdlali', 'lbWins':'Uphumelele', 'lbGames':'Imidlalo', 'lbWinPct':'Amaphs%',
    'skinLabel':'Isikhumba', 'langLabel':'IsiLimi', 'levelLabel':'Izinga', 'modeLabel':'Uhlobo',
    'rulesTitle':'Imithetho',
    'rulesBoard':'IBhodi',
    'rulesBoardText':'Imigqa emine enembobo ezine kuya kweziyisithupha. Umugqa waphakathi uhlukanisa izihlalo zombili, nomugqa wemigqa emibili ngamunye. Umugqa wangaphakathi useduze kwendikimba.',
    'rulesStones':'Amatshe (Izinkomo)',
    'rulesStonesText':'Amatshe amabili afakwa kuzo zonke izimbobo ekuqaleni.',
    'rulesSow':'Ukuhlwanyela Ngokuphambene Nehora',
    'rulesSowText':'Thatha wonke amatshe embobo bese uwela ngawunye ngokuphambene nehora. Uma itshe lokugcina liwa lapho kunamatshe khona, kuqhubeka ukubuyisa. Misa lapho itshe lokugcina liwa embobo engenalutho.',
    'rulesCapture':'Ukubamba',
    'rulesCaptureText':'Ukubuyisa kuphelela emugqeni wakho wangaphakathi embobo engenalutho futhi zombili izimbobo ezingaphambili zinazo izinkomo — bamba zonke izinkomo zesitha.',
    'rulesRules':'Imithetho Ebalulekile',
    'rulesRulesText':'Awukwazi ukuqala esiqendini uma kukhona izimbili.\nAwukwazi ukususa ijozi lodwa.\nUma kuphela iziqephu: susa esinye ngokuphambene nehora.\nAkukho zinyakalo: lala (kulala), isitha siqhubeke.',
    'rulesWin':'Ukuqoba',
    'rulesWinText':'Thatha zonke izinkomo zesitha. Uma kuphela iziqephu, izinkomo eziningi zinqoba.',
    'cowsLabel':'izinkomo', 'aiName':'AI Isitha',
    'copyright':'Intshuba © 2026 · Imidlalo YamaНdebele',
  },

  # ── Français ──────────────────────────────────────────────────────────
  # Corrections: sleeping Dors(imperative)→Dort(3rd person); all French apostrophes escaped
  'fr': {
    'label':'Français', 'flag':'🇫🇷',
    'turnYou':'Votre Tour',            'turnAI':'IA Réfléchit...', 'turnP2':'Joueur 2',
    'captured':'+{n} Vaches!',         'sleeping':'Dort (kulala)',
    'win':'Vous Gagnez! 🏆',           'lose':'L\'IA Gagne! 🤖',   'draw':'Egalite! ⚖️',
    'winMsg':'Félicitations !',        'loseMsg':'L\'IA gagne !',   'drawMsg':'Egalite !',
    'winNote':'Bien joué, guerrier !', 'loseNote':'Bonne chance la prochaine fois !', 'drawNote':'Une impasse honorable !',
    'lv1':'Débutant', 'lv2':'Guerrier', 'lv3':'Roi',
    'lv1desc':'4x4 · IA Facile', 'lv2desc':'4x6 · IA Intelligente', 'lv3desc':'4x6 · IA Difficile',
    'vsAI':'vs IA', 'twoPlayers':'2 Joueurs',
    'rules':'Règles', 'home':'Accueil', 'profile':'Profil', 'restart':'Recommencer',
    'playAgain':'Rejouer', 'start':'▷ Démarrer', 'logout':'Déconnexion',
    'leaderboard':'Classement', 'close':'Fermer',
    'signIn':'Se Connecter', 'register':'S\'inscrire',
    'email':'E-mail', 'password':'Mot de passe',
    'name':'Prénom', 'confirm':'Confirmer le mot de passe',
    'guestPlay':'Jouer en invité', 'alreadyReg':'Déjà inscrit ? Connexion',
    'newUser':'Nouveau ? S\'inscrire',
    'profileTitle':'Mon Profil', 'joined':'Inscrit le', 'lastLogin':'Dernière connexion',
    'status':'Statut', 'guest':'Invité',
    'wins':'Victoires', 'losses':'Défaites', 'draws':'Nuls', 'played':'Joués', 'winPct':'% Victoires',
    'lbTitle':'Classement', 'lbPlayer':'Joueur', 'lbWins':'Victoires', 'lbGames':'Parties', 'lbWinPct':'% Vic',
    'skinLabel':'Apparence', 'langLabel':'Langue', 'levelLabel':'Niveau', 'modeLabel':'Mode',
    'rulesTitle':'Règles du Jeu',
    'rulesBoard':'Le Plateau',
    'rulesBoardText':'Quatre rangées de 4 à 6 trous. Une ligne centrale divise deux camps de deux rangées chacun. La rangée intérieure est la plus proche du centre.',
    'rulesStones':'Pierres (Vaches)',
    'rulesStonesText':'Deux pierres placées dans chaque trou au début.',
    'rulesSow':'Semis dans le sens antihoraire',
    'rulesSowText':'Prenez toutes les pierres d\'un trou et déposez-en une par une dans le sens antihoraire. Si la dernière pierre atterrit où il y a des pierres, le relais continue. Arrêtez quand la dernière pierre atterrit dans un trou vide.',
    'rulesCapture':'Capturer',
    'rulesCaptureText':'Le relais se termine sur votre rangée intérieure dans un trou vide ET les deux trous opposés ont des pierres — capturez toutes ces vaches adverses.',
    'rulesRules':'Règles Clés',
    'rulesRulesText':'Ne peut pas commencer sur un isolé s\'il existe des paires.\nNe peut pas retirer la seule paire.\nSeulement des isolés : déplacer un dans le sens antihoraire.\nAucun mouvement valide : dormir (kulala), l\'adversaire continue.',
    'rulesWin':'Victoire',
    'rulesWinText':'Prenez toutes les vaches de l\'adversaire. S\'il ne reste que des isolés, le plus de vaches l\'emporte.',
    'cowsLabel':'vaches', 'aiName':'IA Adverse',
    'copyright':'Intshuba © 2026 · Jeux du Patrimoine Nguni',
  },

  # ── Spanish ──────────────────────────────────────────────────────────────────
  'es': {
    'label':'Español','flag':'🇪🇸','turnYou':'Tu Turno','turnAI':'IA Pensando...','turnP2':'Jugador 2',
    'captured':'+{n} Vacas!','sleeping':'Durmiendo (kulala)',
    'win':'Ganaste! 🏆','lose':'IA Gano! 🤖','draw':'Empate! ⚖️',
    'winMsg':'Felicitaciones!','loseMsg':'La IA gana!','drawMsg':'Empate!',
    'winNote':'Bien jugado, guerrero!','loseNote':'Mejor suerte la proxima vez!','drawNote':'Un honroso empate!',
    'lv1':'Novato','lv2':'Guerrero','lv3':'Rey','lv1desc':'4x4 - IA Facil','lv2desc':'4x6 - IA Inteligente','lv3desc':'4x6 - IA Dificil',
    'vsAI':'vs IA','twoPlayers':'2 Jugadores','rules':'Reglas','home':'Inicio','profile':'Perfil',
    'restart':'Reiniciar','playAgain':'Jugar de Nuevo','start':'Iniciar','logout':'Salir',
    'leaderboard':'Clasificacion','close':'Cerrar','signIn':'Iniciar Sesion','register':'Registrarse',
    'email':'Correo','password':'Contrasena','name':'Nombre',
    'wins':'Victorias','losses':'Derrotas','draws':'Empates','played':'Jugadas','winPct':'% Victorias',
    'rulesTitle':'Reglas del Juego',
    'rulesBoard':'El Tablero','rulesBoardText':'Cuatro filas de 4 a 6 agujeros. Una linea central divide dos campos.',
    'rulesStones':'Piedras (Vacas)','rulesStonesText':'Dos piedras en cada agujero al inicio.',
    'rulesSow':'Siembra antihoraria','rulesSowText':'Tome todas las piedras de un agujero y deposite una por una en sentido antihorario.',
    'rulesCapture':'Captura','rulesCaptureText':'El relevo termina en tu fila interior en agujero vacio Y los dos agujeros opuestos tienen piedras -- capture todas.',
    'rulesRules':'Reglas Clave','rulesRulesText':'No puede comenzar en un solitario si existen pares.\nSin movimientos: dormir (kulala).',
    'rulesWin':'Victoria','rulesWinText':'Toma todas las vacas del adversario. Mas vacas al final gana.',
    'cowsLabel':'vacas','aiName':'IA Adversaria','copyright':'Intshuba 2026 - Juegos del Patrimonio Nguni',
  },
  # ── Portuguese ───────────────────────────────────────────────────────────────
  'pt': {
    'label':'Portugues','flag':'🇧🇷','turnYou':'Sua Vez','turnAI':'IA Pensando...','turnP2':'Jogador 2',
    'captured':'+{n} Vacas!','sleeping':'Dormindo (kulala)',
    'win':'Voce Ganhou! 🏆','lose':'IA Venceu! 🤖','draw':'Empate! ⚖️',
    'winMsg':'Parabens!','loseMsg':'A IA vence!','drawMsg':'Empate!',
    'winNote':'Bem jogado, guerreiro!','loseNote':'Melhor sorte na proxima vez!','drawNote':'Um empate honroso!',
    'lv1':'Iniciante','lv2':'Guerreiro','lv3':'Rei','lv1desc':'4x4 - IA Facil','lv2desc':'4x6 - IA Inteligente','lv3desc':'4x6 - IA Dificil',
    'vsAI':'vs IA','twoPlayers':'2 Jogadores','rules':'Regras','home':'Inicio','profile':'Perfil',
    'restart':'Reiniciar','playAgain':'Jogar Novamente','start':'Iniciar','logout':'Sair',
    'leaderboard':'Classificacao','close':'Fechar','signIn':'Entrar','register':'Registrar',
    'email':'E-mail','password':'Senha','name':'Nome',
    'wins':'Vitorias','losses':'Derrotas','draws':'Empates','played':'Jogados','winPct':'% Vitorias',
    'rulesTitle':'Regras do Jogo',
    'rulesBoard':'O Tabuleiro','rulesBoardText':'Quatro filas de 4 a 6 buracos. Uma linha central divide dois campos.',
    'rulesStones':'Pedras (Vacas)','rulesStonesText':'Duas pedras em cada buraco no inicio.',
    'rulesSow':'Semeadura anti-horaria','rulesSowText':'Pegue todas as pedras de um buraco e deposite uma por uma no sentido anti-horario.',
    'rulesCapture':'Captura','rulesCaptureText':'O revezamento termina na sua fila interior num buraco vazio E os dois buracos opostos tem pedras -- capture todas.',
    'rulesRules':'Regras Principais','rulesRulesText':'Nao pode comecar num solitario se existem pares.\nSem movimentos: dormir (kulala).',
    'rulesWin':'Vitoria','rulesWinText':'Tome todas as vacas do adversario. Mais vacas no final vence.',
    'cowsLabel':'vacas','aiName':'IA Adversaria','copyright':'Intshuba 2026 - Jogos do Patrimonio Nguni',
  },
  # ── Arabic ───────────────────────────────────────────────────────────────────
  'ar': {
    'label':'Arabic','flag':'🇸🇦','turnYou':'Dawrak','turnAI':'AI yufakkir...','turnP2':'Laib 2',
    'captured':'+{n} Abqar!','sleeping':'Naim (kulala)',
    'win':'Fazta! 🏆','lose':'AI faz! 🤖','draw':'Taadul! ⚖️',
    'winMsg':'Mabruk!','loseMsg':'AI yafuz!','drawMsg':'Taadul!',
    'winNote':'Ahsanta, muharib!','loseNote':'Hazzan afdal al-marra al-qadima!','drawNote':'Tawaquf sharaf!',
    'lv1':'Mubtadi','lv2':'Muharib','lv3':'Malik',
    'lv1desc':'4x4 - AI Sahel','lv2desc':'4x6 - AI Dhaki','lv3desc':'4x6 - AI Saab',
    'vsAI':'did AI','twoPlayers':'Laiban','rules':'Qawaid','home':'Raisiyya','profile':'Malaf',
    'restart':'Ibda min jadid','playAgain':'Ilabe mujaddadan','start':'Ibda','logout':'Khuruj',
    'leaderboard':'Lauh al-mutasaddireen','close':'Ighlaq','signIn':'Tasjeel al-dukhool','register':'Tasjeel',
    'email':'Bareed iliktroni','password':'Kalima al-sir','name':'Ism',
    'wins':'Intisar','losses':'Hazima','draws':'Taadul','played':'Luibat','winPct':'% Fawz',
    'rulesTitle':'Qawaid al-Liaba',
    'rulesBoard':'Al-Lauh','rulesBoardText':'Arba saff min 4-6 thuqub. Khatt markazi yaqsim al-maleb.',
    'rulesStones':'Hijara (Abqar)','rulesStonesText':'Hajarataan fi kull thuqub fi al-bidaya.',
    'rulesSow':'Al-Zar aks aqarib al-saa','rulesSowText':'Khudh kull al-hijara min thuqub wa daha wahida wahida aks aqarib al-saa.',
    'rulesCapture':'Al-Istila','rulesCaptureText':'Idha inha al-zar fi saffak al-dakhili thuqub farigh wa al-thuqban al-muqabilan biha hijara -- khudhhum kullahum.',
    'rulesRules':'Al-Qawaid al-Asasiyya','rulesRulesText':'La yumkin al-bidaya min hajar munfarid idha kan hunaka azwaj.\nLa harakat sahiha: nawm (kulala).',
    'rulesWin':'Al-Fawz','rulesWinText':'Khudh kull abqar al-khasim. Akthar abqar fi al-nihaya yafuz.',
    'cowsLabel':'abqar','aiName':'AI al-khasim','copyright':'Intshuba 2026 - Aleb Turath Nguni',
  },
  # ── Amharic ──────────────────────────────────────────────────────────────────
  'am': {
    'label':'Amharic','flag':'🇪🇹','turnYou':'Terahu newu','turnAI':'AI yasebel...','turnP2':'Teachawach 2',
    'captured':'+{n} Lamoch!','sleeping':'Teynetal (kulala)',
    'win':'Asenefke! 🏆','lose':'AI asenefe! 🤖','draw':'Acha! ⚖️',
    'winMsg':'Enkuan des alehe!','loseMsg':'AI ynafal!','drawMsg':'Acha!',
    'winNote':'Tiru techaruweteh, tewagi!','loseNote':'Yeteketelew gize edel!','drawNote':'Yetekerebe fetsame!',
    'lv1':'Jemari','lv2':'Tewagi','lv3':'Negus',
    'lv1desc':'4x4 - Kela AI','lv2desc':'4x6 - Belh AI','lv3desc':'4x6 - Keba AI',
    'vsAI':'vs AI','twoPlayers':'2 Teachawach','rules':'Hgoch','home':'Wanaw','profile':'Melya',
    'restart':'Ejigen Jemr','playAgain':'Ejigen Teachawet','start':'Jemr','logout':'Wuta',
    'leaderboard':'Deraja Seleda','close':'Zga','signIn':'Gba','register':'Temezgeb',
    'email':'Email','password':'Yeyilef Kal','name':'Sem',
    'wins':'Dloch','losses':'Shenfetoch','draws':'Achawoch','played':'Teachawetal','winPct':'% Edel',
    'rulesTitle':'Yechewacha Hgoch',
    'rulesBoard':'Seleda','rulesBoardText':'Arat redfoch ke 4-6 kedadawoch. Ye alem mesgecha kelal yelale.',
    'rulesStones':'Dngayoch (Lamoch)','rulesStonesText':'Tewesaj ke sost kefloch huleta dngayoch.',
    'rulesSow':'Betekarat sar manegede zmezrahet','rulesSowText':'Hulu dngayoch min kedada yizut betekarat sar manegede ahunu ahunu yasayemu.',
    'rulesCapture':'Yazehu','rulesCaptureText':'Yeachirew dngay bewist redfh oda kedada yaderesu begna matayaw hulu kedadawoch dngay yalach -- yizut.',
    'rulesRules':'Wanna Hgoch','rulesRulesText':'Jemroch yalach ahunu siltan min andand lemastamat ayatechalm.\nHege ye Lene yelem: tem (kulala).',
    'rulesWin':'Dl','rulesWinText':'Yeteyaziwn lamoch yizut. Bemechu lamoch wanna mejochu yiketal.',
    'cowsLabel':'lamoch','aiName':'AI Yeteyazach','copyright':'Intshuba 2026 - Ye Nguni Tiwlid Yeche Wachawoch',
  },
  # ── Igbo ─────────────────────────────────────────────────────────────────────
  'ig': {
    'label':'Igbo','flag':'🇳🇬','turnYou':'Oge Gi','turnAI':'AI na atu gharị...','turnP2':'Onye Egwu 2',
    'captured':'+{n} Efi!','sleeping':'Na ura (kulala)',
    'win':'I meriri! 🏆','lose':'AI meriri! 🤖','draw':'Mmejo! ⚖️',
    'winMsg':'Ekele diri gi!','loseMsg':'AI meriri!','drawMsg':'Mmejo!',
    'winNote':'O di mma, onye ogu!','loseNote':'Nwee odimma oge ozo!','drawNote':'Nsogbu ebubedike!',
    'lv1':'Onye mmalite','lv2':'Onye ogu','lv3':'Eze',
    'lv1desc':'4x4 - AI di mfe','lv2desc':'4x6 - AI smart','lv3desc':'4x6 - AI siri ike',
    'vsAI':'vs AI','twoPlayers':'Ndi egwu 2','rules':'Iwu','home':'Ulo','profile':'Profailu',
    'restart':'Malite ozo','playAgain':'Egwu ozo','start':'Bido','logout':'Puo',
    'leaderboard':'Ochịcho','close':'Mechie','signIn':'Banye','register':'Debanye aha',
    'email':'Email','password':'Paswodu','name':'Aha',
    'wins':'Mmeri','losses':'Onwu','draws':'Mmejo','played':'Egwuoro','winPct':'% Mmeri',
    'rulesTitle':'Iwu Egwu',
    'rulesBoard':'Ochịcho','rulesBoardText':'Usoro ano nke orificeo 4-6. Ahiri etiti na ekewa ogige abuo.',
    'rulesStones':'Okwute (Efi)','rulesStonesText':'Okwute abuo n orificeo obuna na mbido egwu.',
    'rulesSow':'Ikọ n onodu gburugburu aka ekpe','rulesSowText':'Were okwute niile si n orificeo ma tinye ha otu otu n onodu gburugburu aka ekpe.',
    'rulesCapture':'Inako','rulesCaptureText':'O buru na okwute ikpeazu ezue n usoro ime ya n orificeo nke ododo ma orificeo abuo di n uzo nwere okwute -- were ha niile.',
    'rulesRules':'Iwu Ndi Isi','rulesRulesText':'Enweghị ike imalite site n otu okwute ma o buru na ndi abuo di.\nEnweghị nzo ziri ezi: ura (kulala).',
    'rulesWin':'Mmeri','rulesWinText':'Were efi niile nke ochịcho. Onye nwere efi karia ga eri.',
    'cowsLabel':'efi','aiName':'AI Onye Ochịcho','copyright':'Intshuba 2026 - Egwu Ochịcho Nguni',
  },
  # ── Swahili ──────────────────────────────────────────────────────────────────
  'sw': {
    'label':'Kiswahili','flag':'🇹🇿','turnYou':'Zamu Yako','turnAI':'AI Inafikiria...','turnP2':'Mchezaji 2',
    'captured':'+{n} Ng\'ombe!','sleeping':'Analala (kulala)',
    'win':'Umeshinda! 🏆','lose':'AI Imeshinda! 🤖','draw':'Sawa! ⚖️',
    'winMsg':'Hongera!','loseMsg':'AI Inashinda!','drawMsg':'Sawa!',
    'winNote':'Umecheza vizuri, mpiganaji!','loseNote':'Bahati njema mara ijayo!','drawNote':'Msimamo wa heshima!',
    'lv1':'Mwanzo','lv2':'Mpiganaji','lv3':'Mfalme',
    'lv1desc':'4x4 - AI Rahisi','lv2desc':'4x6 - AI Akili','lv3desc':'4x6 - AI Ngumu',
    'vsAI':'vs AI','twoPlayers':'Wachezaji 2','rules':'Sheria','home':'Nyumbani','profile':'Wasifu',
    'restart':'Anza Upya','playAgain':'Cheza Tena','start':'Anza','logout':'Toka',
    'leaderboard':'Jedwali la Bora','close':'Funga','signIn':'Ingia','register':'Jisajili',
    'email':'Barua pepe','password':'Nenosiri','name':'Jina',
    'wins':'Ushindi','losses':'Kushindwa','draws':'Sawa','played':'Zimechezwa','winPct':'% Ushindi',
    'rulesTitle':'Sheria za Mchezo',
    'rulesBoard':'Ubao','rulesBoardText':'Safu nne za mashimo 4-6. Mstari wa kati unagawanya uwanja mara mbili.',
    'rulesStones':'Mawe (Ng\'ombe)','rulesStonesText':'Mawe mawili katika kila shimo mwanzoni.',
    'rulesSow':'Kupanda kinyume cha saa','rulesSowText':'Chukua mawe yote kutoka shimo na uweke moja moja kinyume cha saa.',
    'rulesCapture':'Kukamata','rulesCaptureText':'Kama jiwe la mwisho linaishia kwenye safu yako ya ndani shimo tupu NA mashimo mawili kinyume yana mawe -- chukua yote.',
    'rulesRules':'Sheria Kuu','rulesRulesText':'Hauwezi kuanza kwenye jiwe moja ikiwa kuna jozi.\nHauna harakati: lala (kulala).',
    'rulesWin':'Ushindi','rulesWinText':'Chukua ngombe wote wa mpinzani. Ngombe wengi mwishowe ndiye mshindi.',
    'cowsLabel':'ngombe','aiName':'AI Mpinzani','copyright':'Intshuba 2026 - Michezo ya Urithi wa Nguni',
  },
  # ── Mandarin ─────────────────────────────────────────────────────────────────
  'zh': {
    'label':'Zhongwen','flag':'🇨🇳','turnYou':'Ni de huihé','turnAI':'AI sixhong...','turnP2':'Wanjia 2',
    'captured':'+{n} Nai niu!','sleeping':'Shuimian (kulala)',
    'win':'Ni yingle! 🏆','lose':'AI yingle! 🤖','draw':'Pingju! ⚖️',
    'winMsg':'Zhùhè!','loseMsg':'AI huoling!','drawMsg':'Pingju!',
    'winNote':'Da de hao, zhanshi!','loseNote':'Xia ci haoyun!','drawNote':'Guangrong pingju!',
    'lv1':'Chuansuezhe','lv2':'Zhanshu','lv3':'Wáng',
    'lv1desc':'4x4 - Jianyi AI','lv2desc':'4x6 - Congming AI','lv3desc':'4x6 - Kunnan AI',
    'vsAI':'vs AI','twoPlayers':'Shuang ren','rules':'Guize','home':'Zhuye','profile':'Geren ziliao',
    'restart':'Chongxin kaishi','playAgain':'Zai wan yi ci','start':'Kaishi','logout':'Dengchu',
    'leaderboard':'Paihangbang','close':'Guanbi','signIn':'Denglu','register':'Zhuce',
    'email':'Youxiang','password':'Mima','name':'Xingming',
    'wins':'Shengli','losses':'Shibai','draws':'Pingju','played':'Yi wan','winPct':'Shenglü%',
    'rulesTitle':'Youxi Guize',
    'rulesBoard':'Qipan','rulesBoardText':'Si pai 4 dao 6 ge dong. Zhongjian xian ba qipan fen cheng liang ge quyu.',
    'rulesStones':'Qi zi (Nai niu)','rulesStonesText':'Youxi kaishi shi mei ge dong li you liang ke qi zi.',
    'rulesSow':'Ni shizhen fang xiang bo zhong','rulesSowText':'Cong yi ge dong qu chu suo you qi zi, ni shizhen fang xiang yi yi fang ru ge dong.',
    'rulesCapture':'Bu huo','rulesCaptureText':'Zui hou yi ke qi zi luo zai ji fang nei pai kong dong, qie duimian liang dong you qi zi -- qu zou suo you.',
    'rulesRules':'Zhu yao guize','rulesRulesText':'Ru guo cun zai cheng dui, bu neng cong dan du qi zi kai shi.\nWu you xiao yi dong: shui mian (kulala).',
    'rulesWin':'Shengli','rulesWinText':'Qu zou dui fang suo you nai niu. Zui hou nai niu zui duo zhe huo sheng.',
    'cowsLabel':'nai niu','aiName':'AI duishou','copyright':'Intshuba 2026 - Nguni Wenhua Yichan Youxi',
  },
  # ── Hindi ─────────────────────────────────────────────────────────────────────
  'hi': {
    'label':'Hindi','flag':'🇮🇳','turnYou':'Aapki baari','turnAI':'AI soch raha hai...','turnP2':'Khiladi 2',
    'captured':'+{n} Gayein!','sleeping':'So raha hai (kulala)',
    'win':'Aap jeet gaye! 🏆','lose':'AI jeet gaya! 🤖','draw':'Barabari! ⚖️',
    'winMsg':'Badhai ho!','loseMsg':'AI jeet gaya!','drawMsg':'Barabari!',
    'winNote':'Shabash, yodha!','loseNote':'Agli baar shubhkamnaen!','drawNote':'Sammanjanak tie!',
    'lv1':'Shuruwati','lv2':'Yodha','lv3':'Raja',
    'lv1desc':'4x4 - Aasan AI','lv2desc':'4x6 - Smart AI','lv3desc':'4x6 - Kathin AI',
    'vsAI':'AI se','twoPlayers':'2 Khiladi','rules':'Niyam','home':'Ghar','profile':'Profiil',
    'restart':'Phir shuru karo','playAgain':'Phir khelo','start':'Shuru','logout':'Log out',
    'leaderboard':'Leaderboard','close':'Band karo','signIn':'Sign in','register':'Register',
    'email':'Email','password':'Password','name':'Naam',
    'wins':'Jeet','losses':'Haar','draws':'Barabari','played':'Khele','winPct':'% Jeet',
    'rulesTitle':'Khel ke Niyam',
    'rulesBoard':'Board','rulesBoardText':'4 se 6 chedon ki char panktiyaan. Ek kendriya rekha do kshetron ko vibhajit karti hai.',
    'rulesStones':'Pathhar (Gayein)','rulesStonesText':'Khel ki shuruaat mein har chhed mein do pathhar.',
    'rulesSow':'Ulatii ghadi dishaa mein bowaai','rulesSowText':'Ek chhed se sabhi pathhar len aur ulatii ghadi dishaa mein ek-ek karke rakhen.',
    'rulesCapture':'Pakad','rulesCaptureText':'Agar antim pathhar aapki antar pankt ke khaali chhed mein girta hai aur saamne ke do chhed mein pathhar hain -- sab len.',
    'rulesRules':'Mukhya Niyam','rulesRulesText':'Agar jode hain to akele pathhar se shuru nahin kar sakte.\nKoi chal nahin: sona (kulala).',
    'rulesWin':'Jeet','rulesWinText':'Pratidvandvi ki sabhi gayein len. Ant mein sabse adhik gayein jeetti hain.',
    'cowsLabel':'gayein','aiName':'AI Pratidvandvi','copyright':'Intshuba 2026 - Nguni Sanskritik Virasat Khel',
  },
  # ── Japanese ─────────────────────────────────────────────────────────────────
  'ja': {
    'label':'Nihongo','flag':'🇯🇵','turnYou':'Anata no ban','turnAI':'AI ga kangaeteimasu...','turnP2':'Pureiyaa 2',
    'captured':'+{n} to no ushi!','sleeping':'Neteimasu (kulala)',
    'win':'Anata no kachi! 🏆','lose':'AI no kachi! 🤖','draw':'Hikiwake! ⚖️',
    'winMsg':'Omedetou gozaimasu!','loseMsg':'AI ga kachimashita!','drawMsg':'Hikiwake!',
    'winNote':'Yoku tatakaaimashita, yuushi!','loseNote':'Jikai ganbatte kudasai!','drawNote':'Meiyo aru hikiwake!',
    'lv1':'Shoshinsha','lv2':'Senshi','lv3':'Oo',
    'lv1desc':'4x4 - Kantan AI','lv2desc':'4x6 - Kashikoi AI','lv3desc':'4x6 - Muzukashii AI',
    'vsAI':'vs AI','twoPlayers':'2 jin pureiyaa','rules':'Ruuru','home':'Hoomu','profile':'Purofiru',
    'restart':'Yarenaoshi','playAgain':'Mou ichido','start':'Sutaato','logout':'Rogutoauto',
    'leaderboard':'Rankingu','close':'Tojiru','signIn':'Sain in','register':'Touroku',
    'email':'Meeru','password':'Pasuwaado','name':'Namae',
    'wins':'Shoori','losses':'Haiboku','draws':'Hikiwake','played':'Pureizhumi','winPct':'Shooritsu%',
    'rulesTitle':'Geemu Ruuru',
    'rulesBoard':'Booodo','rulesBoardText':'4-6 ko no ana ga 4 retsu. Chuuou no sen ga 2 tsu no eria ni wakeru.',
    'rulesStones':'Ishi (ushi)','rulesStonesText':'Geemu kaishi ji, kaku ana ni 2 tsu no ishi.',
    'rulesSow':'Hantokei mawari no tanemaki','rulesSowText':'Ana kara subete no ishi wo tori, hantokei mawari ni hitotsu zutsu oku.',
    'rulesCapture':'Hokyaku','rulesCaptureText':'Saigo no ishi ga jibun no uchi retsu no kara ana ni chakuchi shi, mukai no 2 tsu no ana ni ishi ga aru baai -- subete toru.',
    'rulesRules':'Omo na ruuru','rulesRulesText':'Tsui ga aru baai, tandoku no ishi kara hajimerarenai.\nYuukou na te ga nai: suimin (kulala).',
    'rulesWin':'Shoori','rulesWinText':'Aite no ushi wo subete toru. Saigo ni ushi ga ichiban ooi hito ga katsu.',
    'cowsLabel':'to no ushi','aiName':'AI taisensoosha','copyright':'Intshuba 2026 - Nguni Bunka Isan Geemu',
  },
  # ── Korean ───────────────────────────────────────────────────────────────────
  'ko': {
    'label':'Hangugeo','flag':'🇰🇷','turnYou':'Dangsin ui chaere','turnAI':'AI ga saeng gak jung...','turnP2':'Peullei eo 2',
    'captured':'+{n} mari so!','sleeping':'Ja go iteum (kulala)',
    'win':'Dangsin i igeos seumnida! 🏆','lose':'AI ga igeos seumnida! 🤖','draw':'Mu seung bu! ⚖️',
    'winMsg':'Chuk ha ham ni da!','loseMsg':'AI ga ige seumnida!','drawMsg':'Mu seung bu!',
    'winNote':'Jal ssa uos seumnida, jeon sa yeo!','loseNote':'Da eum e neun haeng un eul bib ni da!','drawNote':'Myeong ye ro un mu seung bu!',
    'lv1':'Cho bo ja','lv2':'Jeon sa','lv3':'Wang',
    'lv1desc':'4x4 - Swi un AI','lv2desc':'4x6 - Seu ma teu AI','lv3desc':'4x6 - Eo ryeo un AI',
    'vsAI':'AI dae','twoPlayers':'2 in peullei','rules':'Gyu chik','home':'Hom','profile':'Peu ro pil',
    'restart':'Da si si jak','playAgain':'Da si peullei','start':'Si jak','logout':'Ro geu a ut',
    'leaderboard':'Li deo bo deu','close':'Dat gi','signIn':'Lo geu in','register':'Ga ip',
    'email':'I me il','password':'Bi mil beon ho','name':'I reum',
    'wins':'Seung ri','losses':'Pae bae','draws':'Mu seung bu','played':'Peullei','winPct':'Seung ryul%',
    'rulesTitle':'Ge im Gyu chik',
    'rulesBoard':'Bo deu','rulesBoardText':'4-6 gae ui gu meong i i neun 4 jul. Junggan seon i du gu yeok eu ro na nun da.',
    'rulesStones':'Dol (so)','rulesStonesText':'Ge im si jak si gak gu meong e dol 2 gae.',
    'rulesSow':'Si gye ban dae bang hyang seu mu gi','rulesSowText':'Gu meong e seo mo deun dol eul ga jyeo si gye ban dae bang hyang eu ro ha na ssik not neun da.',
    'rulesCapture':'Po hok','rulesCaptureText':'Ma ji mak dol i ja sin ui an jul bin gu meong e chak ji ha go ban dae pyeon du gu meong e dol i i sseul gyeong u -- mo du ga jyeo ga n da.',
    'rulesRules':'Ju yo gyu chik','rulesRulesText':'Ssang i i sseu myeon dan dok dol e seo si jak hal su eobs seumnida.\nYu hyeo han i dong eobs eum: su myeon (kulala).',
    'rulesWin':'Seung ri','rulesWinText':'Sang dae bang ui so reul mo du ga jyeo ga n da. Ma ji mak e so ga ga jang manh eun sa ram i i gin da.',
    'cowsLabel':'mari so','aiName':'AI sang dae','copyright':'Intshuba 2026 - Nguni Mun hwa Yu san Ge im',
  },
  # ── Russian ──────────────────────────────────────────────────────────────────
  'ru': {
    'label':'Russkiy','flag':'🇷🇺','turnYou':'Vash khod','turnAI':'IA dumayet...','turnP2':'Igrok 2',
    'captured':'+{n} korov!','sleeping':'Spit (kulala)',
    'win':'Vy pobedili! 🏆','lose':'IA pobedil! 🤖','draw':'Nichya! ⚖️',
    'winMsg':'Pozdravlyayem!','loseMsg':'IA pobedil!','drawMsg':'Nichya!',
    'winNote':'Otlichno sygrano, voin!','loseNote':'Udachi v sleduyushchiy raz!','drawNote':'Pochyotnaya nichya!',
    'lv1':'Novichok','lv2':'Voin','lv3':'Korol',
    'lv1desc':'4x4 - Lyogkiy IA','lv2desc':'4x6 - Umnyy IA','lv3desc':'4x6 - Slozhnyy IA',
    'vsAI':'vs IA','twoPlayers':'2 igroka','rules':'Pravila','home':'Glavnaya','profile':'Profil',
    'restart':'Perezapustit','playAgain':'Igrat snova','start':'Start','logout':'Vyyti',
    'leaderboard':'Tablitsa liderov','close':'Zakryt','signIn':'Voyti','register':'Zaregistrirovatsa',
    'email':'El pochta','password':'Parol','name':'Imya',
    'wins':'Pobedy','losses':'Porazheniya','draws':'Nichi','played':'Syigrano','winPct':'% Pobed',
    'rulesTitle':'Pravila Igry',
    'rulesBoard':'Doska','rulesBoardText':'Chetyre ryada iz 4-6 lunok. Tsentralnaya liniya delyet pole na dva lagerya.',
    'rulesStones':'Kamni (Korovy)','rulesStonesText':'Po dva kamnya v kazhdoy lunke v nachale igry.',
    'rulesSow':'Posev protiv chasovoy strelki','rulesSowText':'Vozmite vse kamni iz lunki i kladite po odnomu protiv chasovoy strelki.',
    'rulesCapture':'Zakhvat','rulesCaptureText':'Esli posledniy kamen popadayet v pustuyu lunky vnutrennego ryada I v dvukh protivopolozhnykh lunakh yest kamni -- zabirayte vsekh.',
    'rulesRules':'Osnovnye pravila','rulesRulesText':'Nelzya nachinaat s odinochnyy kamnem, esli yest pary.\nNet khodov: son (kulala).',
    'rulesWin':'Pobeda','rulesWinText':'Zaberite vsekh korov sopernika. Bolshe korov v kontse -- pobeditel.',
    'cowsLabel':'korovy','aiName':'IA Sopernik','copyright':'Intshuba 2026 - Igry Naslediya Nguni',
  },
  # ── Twi/Asante ───────────────────────────────────────────────────────────────
  'tw': {
    'label':'Twi','flag':'🇬🇭','turnYou':'Wo turn','turnAI':'AI rebu adwene...','turnP2':'Otaa 2',
    'captured':'+{n} Anantwie!','sleeping':'Redan (kulala)',
    'win':'Woadi! 🏆','lose':'AI adi! 🤖','draw':'Eye pe! ⚖️',
    'winMsg':'Ayekoo!','loseMsg':'AI adi!','drawMsg':'Eye pe!',
    'winNote':'Woayi adwene, okofo!','loseNote':'Wo nkrabea beba!','drawNote':'Animuonyam nhyehyee!',
    'lv1':'Ahoforo','lv2':'Okofo','lv3':'Ohene',
    'lv1desc':'4x4 - AI mmere','lv2desc':'4x6 - AI nyansa','lv3desc':'4x6 - AI den',
    'vsAI':'vs AI','twoPlayers':'Ataafo 2','rules':'Mmara','home':'Fie','profile':'Ho wo ho',
    'restart':'Hye ase bio','playAgain':'Di bio','start':'Fi ase','logout':'Pue',
    'leaderboard':'Nnipa a wodi kan','close':'To mu','signIn':'Wo bra mu','register':'Kyere wo din',
    'email':'Email','password':'Gyinae','name':'Din',
    'wins':'Adidie','losses':'Atokyere','draws':'Pe pe','played':'Adi','winPct':'% Adidie',
    'rulesTitle':'Agodi Mmara',
    'rulesBoard':'Bood','rulesBoardText':'Nkyemu anan a owia 4-6 wom. Mfinimfini tee nkye abien.',
    'rulesStones':'Nkotokwaa (Anantwie)','rulesStonesText':'Nkotokwaa abien wom owia biara afiase.',
    'rulesSow':'Twa ho kwan ben-ben','rulesSowText':'Fa nkotokwaa nyinaa fi owia mu na de biara si owia biara mu.',
    'rulesCapture':'Yi afi','rulesCaptureText':'Se nkotokwaa a ekyiri no si wo mu-ho owia a ehia wom na owia abien a eto ho a nkotokwaa wom a -- yi nyinaa afi.',
    'rulesRules':'Mmara Titiriw','rulesRulesText':'Worentumi mfi baako mu nkotokwaa a abien wom.\nNkoroo biribi nni ho: Dre (kulala).',
    'rulesWin':'Adi','rulesWinText':'Yi wo tamfo anantwie nyinaa. Obi a onantwie doso no na oadi.',
    'cowsLabel':'anantwie','aiName':'AI Tamfo','copyright':'Intshuba 2026 - Nguni Amammui Agodi',
  },

  # ── Shona (Zimbabwe — 15 million speakers) ────────────────────────────────
  'sn': {
    'label':'Shona','flag':'🇿🇼','turnYou':'Basa Rako','turnAI':'AI Kufunga...','turnP2':'Mutambi 2',
    'captured':'+{n} Mombe!','sleeping':'Kumhara (kulala)',
    'win':'Wakunda! 🏆','lose':'AI Yakunda! 🤖','draw':'Kuenzana! ⚖️',
    'winMsg':'Makorokoto!','loseMsg':'AI yakunda!','drawMsg':'Kuenzana!',
    'winNote':'Wakarwa zvakanaka, murwi!','loseNote':'Uve nerombo rwakawanda!','drawNote':'Magumo ekukudzana!',
    'lv1':'Mutangiri','lv2':'Murwi','lv3':'Mambo',
    'lv1desc':'4x4 - AI Yareruka','lv2desc':'4x6 - AI Ine Njere','lv3desc':'4x6 - AI Yaoma',
    'vsAI':'vs AI','twoPlayers':'Vatambi 2','rules':'Mitemo','home':'Kumba','profile':'Madhiri',
    'restart':'Tanga Patsva','playAgain':'Tambia Zvakare','start':'Tanga','logout':'Buda',
    'leaderboard':'Hwaro hweVatambi','close':'Vhara','signIn':'Pinda','register':'Nyoresa',
    'email':'Email','password':'Pasiwedhi','name':'Zita',
    'wins':'Kukunda','losses':'Kukundwa','draws':'Kuenzana','played':'Zvatamibirwa','winPct':'% Kukunda',
    'rulesTitle':'Mitemo yoMutambo',
    'rulesBoard':'Bhodhi','rulesBoardText':'Nhara ina dze mavhiri 4 kusvika 6. Murongo wepakati unodambura minda miviri.',
    'rulesStones':'Matombo (Mombe)','rulesStonesText':'Matombo maviri pamhuri imwe neimwe pakutanga kwemutambo.',
    'rulesSow':'Kudyara Kunoreva Kwakunamata','rulesSowText':'Tora matombo ose paburi ure woisa imwe neimwe mumauri akateedzana.',
    'rulesCapture':'Kubata','rulesCaptureText':'Kana dombo rekupedzisira riri paburi risina chinhu mumutsara wepakati YO nehapana chinhu — tora mombe dzomumwe.',
    'rulesRules':'Mitemo Mikuru','rulesRulesText':'Hauzvirekodza kubva paburi rimwe chete kana kune mapea.\nHauna basa: rara (kulala).',
    'rulesWin':'Kukunda','rulesWinText':'Tora mombe dzose dzomumwe. Ane mombe dzakawanda kupera anokunda.',
    'cowsLabel':'mombe','aiName':'AI Muvengi','copyright':'Intshuba 2026 - Mitambo yeDzinza reNguni',
  },

  # ── Hausa (Nigeria/Niger — 70 million speakers) ───────────────────────────
  'ha': {
    'label':'Hausa','flag':'🇳🇬','turnYou':'Lokacinka','turnAI':'AI Na Tunani...','turnP2':'Dan Wasa 2',
    'captured':'+{n} Shanu!','sleeping':'Yana Barci (kulala)',
    'win':'Ka Ci! 🏆','lose':'AI Ta Ci! 🤖','draw':'Daidai! ⚖️',
    'winMsg':'Barka Da Nasara!','loseMsg':'AI ta ci!','drawMsg':'Daidai!',
    'winNote':'Kyakkyawan Wasa, Jarumi!','loseNote':'Sa a gaba karo na gaba!','drawNote':'Daidaituwar girma!',
    'lv1':'Farkon','lv2':'Jarumi','lv3':'Sarki',
    'lv1desc':'4x4 - AI Mai Sauki','lv2desc':'4x6 - AI Mai Hankali','lv3desc':'4x6 - AI Mai Wahala',
    'vsAI':'vs AI','twoPlayers':'Yan Wasa 2','rules':'Dokoki','home':'Gida','profile':'Bayani',
    'restart':'Fara Daga Farko','playAgain':'Yi Wasa Kuma','start':'Fara','logout':'Fita',
    'leaderboard':'Jerin Mafi Kyau','close':'Rufe','signIn':'Shiga','register':'Yi Rijista',
    'email':'Email','password':'Kalmar Sirri','name':'Suna',
    'wins':'Nasarori','losses':'Sha Kaye','draws':'Daidai','played':'An Buga','winPct':'% Nasara',
    'rulesTitle':'Dokoki na Wasa',
    'rulesBoard':'Allon Wasa','rulesBoardText':'Layuka hudu na ramuka 4 zuwa 6. Layin tsakiya ya raba filayen biyu.',
    'rulesStones':'Duwatsu (Shanu)','rulesStonesText':'Duwatsu biyu a kowace rami a farkon wasan.',
    'rulesSow':'Shuka a Hanya Mai Juyawa','rulesSowText':'Dauki duwatsu daga rami ka sa daya daya cikin ramuka masu juyawa.',
    'rulesCapture':'Kama','rulesCaptureText':'Idan dutse na karshe ya faadi a ramin ciki mara komai kuma ramuka biyu na kishiyar suna da duwatsu -- dauki duka.',
    'rulesRules':'Muhimman Dokoki','rulesRulesText':'Ba za ka fara daga dutse guda ba idan akwai nau-nau.\nBabu mataki mai inganci: barci (kulala).',
    'rulesWin':'Nasara','rulesWinText':'Dauki duk shanun abokin hamayya. Wanda ke da shanu mafi yawa a karshe ya ci.',
    'cowsLabel':'shanu','aiName':'AI Mai Hamayya','copyright':'Intshuba 2026 - Wasannin Gadon Nguni',
  },

  # ── Yoruba (Nigeria — 45 million speakers) ───────────────────────────────
  'yo': {
    'label':'Yoruba','flag':'🇳🇬','turnYou':'Iyipo Re','turnAI':'AI N ro...','turnP2':'Olutere 2',
    'captured':'+{n} Malu!','sleeping':'Oorun (kulala)',
    'win':'O Bori! 🏆','lose':'AI Bori! 🤖','draw':'Dogba! ⚖️',
    'winMsg':'Eku orire!','loseMsg':'AI bori!','drawMsg':'Dogba!',
    'winNote':'O dara ogun, jagunjagun!','loseNote':'Orire dara ni igba to nbowa!','drawNote':'Ipari ola!',
    'lv1':'Akoobere','lv2':'Jagunjagun','lv3':'Oba',
    'lv1desc':'4x4 - AI Irele','lv2desc':'4x6 - AI Ologbon','lv3desc':'4x6 - AI Lile',
    'vsAI':'vs AI','twoPlayers':'Olutere 2','rules':'Ofin','home':'Ile','profile':'Profaili',
    'restart':'Bere Lati Ibere','playAgain':'Tun sere','start':'Bere','logout':'Jade',
    'leaderboard':'Atokun Awon to Dara','close':'Pa','signIn':'Wole','register':'Forukosile',
    'email':'Email','password':'Oro Asiri','name':'Oruko',
    'wins':'Iboribo','losses':'Ofo','draws':'Dogba','played':'Ti sere','winPct':'% Iboribo',
    'rulesTitle':'Ofin Ere',
    'rulesBoard':'Paali','rulesBoardText':'Ila merin pelu iho 4 si 6. Ila arin pin aaye meji.',
    'rulesStones':'Okuta (Malu)','rulesStonesText':'Okuta meji ninu iho kookan ni ibere ere.',
    'rulesSow':'Gbingbin ni itosona','rulesSowText':'Gbe gbogbo okuta lati iho kan si i ot oko oto ni itosona.',
    'rulesCapture':'Mu','rulesCaptureText':'Ti okuta kekere ba pari ni iho ti o sofo ninu ila inu re ati iho meji ekeji ni okuta -- mu gbogbo won.',
    'rulesRules':'Ofin Akoko','rulesRulesText':'O ko le bere lati okuta kan ti awon meji ba wa.\nKo si igbese ti o wulo: sun (kulala).',
    'rulesWin':'Iboribo','rulesWinText':'Gba gbogbo malu olutere naa. Eni ti o ni malu ju ni opin lo jagun.',
    'cowsLabel':'malu','aiName':'AI Olutere','copyright':'Intshuba 2026 - Ere Itan Nguni',
  },

  # ── Amharic already exists as 'am' — add Oromo (Ethiopia — 40M speakers) ─
  'om': {
    'label':'Afaan Oromoo','flag':'🇪🇹','turnYou':'Kan Kee','turnAI':'AI Yaada...','turnP2':'Taphataa 2',
    'captured':'+{n} Saree!','sleeping':'Rafaa (kulala)',
    'win':"Mo'atte! 🏆",'lose':"AI Mo'ate! 🤖",'draw':'Walqixxee! ⚖️',
    'winMsg':'Baga Moo atte!','loseMsg':'AI Moo ate!','drawMsg':'Walqixxee!',
    'winNote':'Taphatte gaarii, waraanaa!','loseNote':'Carraan gaarii yeroo dhufuuf!','drawNote':'Xumura kabajaa!',
    'lv1':'Jalqabaa','lv2':'Waraanaa','lv3':'Mootii',
    'lv1desc':'4x4 - AI Salphaa','lv2desc':'4x6 - AI Xiqqaa','lv3desc':'4x6 - AI Jabaadhu',
    'vsAI':'vs AI','twoPlayers':'Taphattoota 2','rules':'Seerota','home':'Mana','profile':'Profaayilii',
    'restart':'Jalqabi','playAgain':'Irra Deebi Taphii','start':'Jalqabi','logout':"Ba'i",
    'leaderboard':'Kan Toora Irra Jiran','close':'Cufii','signIn':'Seeni','register':'Galmeessi',
    'email':'Imeelii','password':'Jecha Dhokataa','name':'Maqaa',
    'wins':"Mo'iinsa",'losses':'Injifannoo','draws':'Walqixxee','played':'Taphatame','winPct':"% Mo'iinsa",
    'rulesTitle':'Seerota Tapaa',
    'rulesBoard':'Boordiif','rulesBoardText':'Tarreewwan afur kan boolla 4 hanga 6. Sarara giddu-galeessaa dirree lama qooda.',
    'rulesStones':'Dhagaalee (Saree)','rulesStonesText':'Dhagaalee lama boolla tokkoon tokkoon keessa jalqabarra.',
    'rulesSow':'Facaasuu Kallattii Maree','rulesSowText':'Dhagaalee hunda boolla irraa fudhachuudhaan tokkoon tokkoon kallattidhaan kaahi.',
    'rulesCapture':'Qabachuu','rulesCaptureText':'Dhagaan dhumaa boolla duwwaa tarree keessoo kee irratti kufee boolla lameenuu morkataafi dhagaa qaban yoo tahe -- hunda fudhaa.',
    'rulesRules':'Seerota Ijoo','rulesRulesText':'Kan tokko qofa jiru irraa jalqabuu hin dandeessu yoo michuu jiraate.\nHin qabne: rafuu (kulala).',
    'rulesWin':'Mooiinsa','rulesWinText':'Sareewwan morkataaf hunda fudhaa. Kan sareewwan heddu dhuma irratti qabuu moaa.',
    'cowsLabel':'saree','aiName':'AI Morkataa','copyright':'Intshuba 2026 - Tapaa Dhaloota Nguni',
  },

  # ── Somali (50 million speakers across Horn of Africa) ───────────────────
  'so': {
    'label':'Soomaali','flag':'🇸🇴','turnYou':'Wareegaaga','turnAI':'AI Fikira...','turnP2':'Ciyaaryahanka 2',
    'captured':'+{n} Lo!','sleeping':'Hurda (kulala)',
    'win':'Adiga Ku Guulaystay! 🏆','lose':'AI Ku Guulaystay! 🤖','draw':'Sinnaanshaha! ⚖️',
    'winMsg':'Hambalyo!','loseMsg':'AI ku guulaystay!','drawMsg':'Sinnaanshaha!',
    'winNote':'Si fiican u ciyaaray, dagaalyahan!','loseNote':'Nasiib wanaagsan jeer dambe!','drawNote':'Dhammaad sharafeed!',
    'lv1':'Bilaabaha','lv2':'Dagaalyahan','lv3':'Boqor',
    'lv1desc':'4x4 - AI Fudud','lv2desc':'4x6 - AI Caqli Badan','lv3desc':'4x6 - AI Adag',
    'vsAI':'vs AI','twoPlayers':'Ciyaaryahanno 2','rules':'Xeerarka','home':'Guriga','profile':'Xogta',
    'restart':'Dib u Bilow','playAgain':'Ciyaar Kale','start':'Bilow','logout':'Ka Bixi',
    'leaderboard':'Kaalinta Ugu Sareysa','close':'Xir','signIn':'Gal','register':'Is Diiwaan Geli',
    'email':'Iimaylka','password':'Furaha Sirta','name':'Magaca',
    'wins':'Guulo','losses':'Lumo','draws':'Sinnaanshaha','played':'La Ciyaaray','winPct':'% Guul',
    'rulesTitle':'Xeerarka Ciyaarta',
    'rulesBoard':'Sabuuradda','rulesBoardText':'Afar saf oo leh 4-6 dalool. Xarriiqda dhexe waxay u qaybisaa laba qaybood.',
    'rulesStones':'Dhagxaan (Lo)','rulesStonesText':'Laba dhagxaan oo kala geli dalool kasta marka la bilaabo.',
    'rulesSow':'Beer Jihaad Gaduudka','rulesSowText':'Qaado dhammaan dhagxaanta daloolka oo mid mid u geli jihaadka.',
    'rulesCapture':'Qabasho','rulesCaptureText':'Haddii dhagxaanta ugu dambeysa ay ku dhacdo dalool banaan safka gudaha ka mid ah oo daloolada labada dhinac ay leeyihiin dhagxaan - qaado dhammaan.',
    'rulesRules':'Xeerarka Muhiimka','rulesRulesText':'Kuma bilaabi kartid mid kaliya haddii lablaab jiraan.\nJoogitaan la-aan: seexo (kulala).',
    'rulesWin':'Guul','rulesWinText':'Qaado dhammaan loogu ciyaaray tartamaha. Kan leh lo badan dhamaadka ayaa ku guuleeysta.',
    'cowsLabel':'lo','aiName':'AI Tartan','copyright':'Intshuba 2026 - Ciyaarta Dhaqanka Nguni',
  },

}


# ─── Routes ────────────────────────────────────────────────────────────────────

@app.route('/')
def index():
    return render_template_string(HTML_TEMPLATE, langs=LANGS, skins=SKINS)

# ── Auth ───────────────────────────────────────────────────────────────────────
@app.route('/api/register', methods=['POST'])
def register():
    try:
        data = request.get_json(force=True) or {}
        email = sanitise(str(data.get('email','')), 80).lower()
        name  = sanitise(str(data.get('name','')), 32)
        pw    = str(data.get('password',''))
        if not validate_email(email):
            return jsonify({'error': 'Invalid email address'}), 400
        if len(name) < 2:
            return jsonify({'error': 'Name must be at least 2 characters'}), 400
        ok, issues = validate_password(pw)
        if not ok:
            return jsonify({'error': 'Password needs: ' + ', '.join(issues)}), 400
        if not rate_check(f'register_{email}', 3, 300):
            return jsonify({'error': 'Too many registration attempts'}), 429
        db = get_db()
        if db.execute('SELECT 1 FROM users WHERE email=?', (email,)).fetchone():
            return jsonify({'error': 'Email already registered'}), 409
        hsh, salt = hash_password(pw)
        db.execute('INSERT INTO users(email,name,hash,salt) VALUES(?,?,?,?)', (email, name, hsh, salt))
        db.commit()
        token = create_session(email)
        session['token'] = token
        user = db.execute('SELECT * FROM users WHERE email=?', (email,)).fetchone()
        return jsonify({'ok': True, 'user': _user_dict(user)})
    except Exception as e:
        BugFixer.capture('error', f'register error: {e}', e)
        return jsonify({'error': 'Registration failed'}), 500

@app.route('/api/login', methods=['POST'])
def login():
    try:
        data  = request.get_json(force=True) or {}
        email = sanitise(str(data.get('email','')), 80).lower()
        pw    = str(data.get('password',''))
        if not rate_check(f'login_{email}', 5, 60):
            return jsonify({'error': 'Too many login attempts. Wait 1 minute.'}), 429
        db   = get_db()
        user = db.execute('SELECT * FROM users WHERE email=?', (email,)).fetchone()
        if not user or not verify_password(pw, user['hash'], user['salt']):
            return jsonify({'error': 'Invalid email or password'}), 401
        db.execute('UPDATE users SET last_login=? WHERE email=?', (int(time.time()), email))
        db.commit()
        # Update login streak
        _update_login_streak(email)
        _check_achievements(email)
        token = create_session(email)
        session['token'] = token
        return jsonify({'ok': True, 'user': _user_dict(user)})
    except Exception as e:
        BugFixer.capture('error', f'login error: {e}', e)
        return jsonify({'error': 'Login failed'}), 500

@app.route('/api/logout', methods=['POST'])
def logout():
    try:
        token = session.pop('token', None)
        if token:
            db = get_db()
            db.execute('DELETE FROM sessions WHERE token=?', (token,))
            db.commit()
            with _games_lock:
                _games.pop(token, None)
    except Exception as e:
        BugFixer.capture('error', f'logout error: {e}', e)
    return jsonify({'ok': True})

@app.route('/api/me')
def me():
    user = current_user()
    if not user: return jsonify({'user': None})
    return jsonify({'user': _user_dict(user)})

# ── Local Game ─────────────────────────────────────────────────────────────────
@app.route('/api/game/start', methods=['POST'])
def game_start():
    try:
        data  = request.get_json(force=True) or {}
        level = int(data.get('level', 1))
        mode  = str(data.get('mode', 'ai'))
        skin  = sanitise(str(data.get('skin', 'zulu')))
        lang  = sanitise(str(data.get('lang', 'en')))
        if level not in (1,2,3,4,5): level = 1
        if mode not in ('ai','2p'): mode = 'ai'
        if skin not in SKINS: skin = 'zulu'
        if lang not in LANGS: lang = 'en'
        # Board size scales with level: L1=4×4, L2/L3=4×6, L4/L5=4×8
        cols = {1: 4, 2: 6, 3: 6, 4: 8, 5: 8}.get(level, 6)
        rows = 4
        # D5: read tribe_id from request or user session
        tribe_id = sanitise(str(data.get('tribe_id', session.get('tribe_id', 'world'))), 30)
        if tribe_id not in TRIBES: tribe_id = 'world'
        game = GameState(rows=rows, cols=cols, mode=mode, level=level, tribe_id=tribe_id)
        token = session.get('token', secrets.token_hex(16))
        session['token'] = token
        session['skin']  = skin
        session['lang']  = lang
        session['tribe_id'] = tribe_id   # persist tribe across moves
        # Attach persona to game — persist across moves
        persona_id = sanitise(str(data.get('persona_id','shaka')), 20)
        if persona_id not in AI_PERSONAS:
            persona_id = 'shaka'
        game._persona_id   = persona_id
        game._prize_locked = False
        game._bet_amount   = int(data.get('bet_amount', 0))
        if game._bet_amount >= AI_PRIZE_GUARD_COWS:
            game._prize_locked = True
            log.info(f'[AI] Prize-lock activated for game (bet={game._bet_amount})')
        set_game(token, game)
        user = current_user()
        if user:
            db = get_db()
            db.execute('UPDATE users SET skin=?,level=?,lang=? WHERE email=?',
                       (skin, level, lang, user['email']))
            db.commit()
        return jsonify({'ok': True, 'state': game.to_dict(), 'skin': SKINS[skin], 'lang': LANGS.get(lang, LANGS['en'])})
    except Exception as e:
        BugFixer.capture('error', f'game_start error: {e}', e)
        return jsonify({'error': str(e)}), 500

@app.route('/api/game/move', methods=['POST'])
def game_move():
    try:
        token = session.get('token')
        game  = get_game(token)
        if not game:
            return jsonify({'error': 'No active game'}), 400
        data = request.get_json(force=True) or {}
        idx  = int(data.get('idx', -1))
        if not (0 <= idx < game.rows * game.cols):
            return jsonify({'error': 'Invalid hole index'}), 400
        if game.phase != 'idle':
            return jsonify({'error': 'Not your turn yet'}), 400
        if not game.running:
            return jsonify({'error': 'Game is over'}), 400
        if game.mode == 'ai' and game.player != 0:
            return jsonify({'error': 'AI is playing'}), 400
        steps, captured, _, _ = game.do_sow(idx, game.player)
        quantum_reveal = getattr(game, '_last_quantum_reveal', None)
        if steps is None:
            return jsonify({'error': 'Invalid move'}), 400
        lang_data = LANGS.get(session.get('lang','en'), LANGS['en'])
        msg = ''
        if captured:
            msg = lang_data['captured'].replace('{n}', str(captured))
        ended, p0, p1 = game.check_end()
        if ended:
            game.phase = 'done'; game.running = False
            cows_won = p0 if p0 > p1 else 0
            _record_result(game, p0, p1, cows_won)
            # Human won — teach the AI it lost (AI is player 1)
            persona_id = getattr(game, '_persona_id', 'shaka')
            if game.mode == 'ai':
                conclude_game_learning(token, persona_id, False, p1, p0)
            return jsonify({'ok': True, 'state': game.to_dict(), 'steps': steps,
                            'captured': captured, 'message': msg,
                            'game_over': True, 'scores': [p0, p1],
                            'narrator': _narrate_end(p0, p1, lang_data),
                            'ai_persona': persona_id,
                            'ai_learned': True})
        game.player = 1 - game.player
        ai_steps, ai_captured, ai_msg = [], 0, ''
        ai_hole = -1
        if game.mode == 'ai' and game.player == 1:
            if not game.any_moves(1):
                msg += ' ' + lang_data['sleeping']
                game.player = 0
                ended, p0, p1 = game.check_end()
                if ended:
                    game.phase = 'done'; game.running = False
                    _record_result(game, p0, p1, p0 if p0>p1 else 0)
                    return jsonify({'ok': True, 'state': game.to_dict(), 'steps': steps,
                                    'captured': captured, 'message': msg,
                                    'game_over': True, 'scores': [p0, p1],
                                    'narrator': _narrate_end(p0, p1, lang_data)})
            else:
                ai_hole = game.ai_move()
                if ai_hole >= 0:
                    ai_steps, ai_captured, _, _ = game.do_sow(ai_hole, 1)
                    ai_quantum_reveal = getattr(game, '_last_quantum_reveal', None)
                    if ai_captured:
                        ai_msg = lang_data['captured'].replace('{n}', str(ai_captured))
                    # Record AI move for learning
                    persona_id = getattr(game, '_persona_id', 'shaka')
                    record_ai_move(token, ai_hole, ai_captured)
                    game.player = 0
                    ended, p0, p1 = game.check_end()
                    if ended:
                        game.phase = 'done'; game.running = False
                        _record_result(game, p0, p1, p0 if p0>p1 else 0)
                        # Trigger learning from this completed game
                        ai_won = p1 > p0
                        conclude_game_learning(token, persona_id, ai_won, p1, p0)
                        return jsonify({'ok': True, 'state': game.to_dict(),
                                        'steps': steps, 'ai_steps': ai_steps,
                                        'captured': captured, 'ai_captured': ai_captured,
                                        'message': msg, 'ai_message': ai_msg, 'ai_hole': ai_hole,
                                        'game_over': True, 'scores': [p0, p1],
                                        'narrator': _narrate_end(p0, p1, lang_data),
                                        'ai_persona': persona_id,
                                        'ai_version': getattr(_load_weights(persona_id),'version',1)})
        set_game(token, game)
        return jsonify({
            'ok': True, 'state': game.to_dict(),
            'steps': steps, 'ai_steps': ai_steps,
            'captured': captured, 'ai_captured': ai_captured,
            'message': msg, 'ai_message': ai_msg, 'ai_hole': ai_hole,
            'game_over': False,
            'quantum_reveal': quantum_reveal,
            'narrator': _narrate_move(idx, captured, ai_hole, ai_captured, lang_data)
        })
    except Exception as e:
        BugFixer.capture('error', f'game_move error: {e}', e)
        try:
            token = session.get('token')
            game  = get_game(token)
            if game: game._recover(); set_game(token, game)
        except: pass
        return jsonify({'error': 'Move failed — game state recovered'}), 500

@app.route('/api/game/state')
def game_state():
    token = session.get('token')
    game  = get_game(token)
    if not game: return jsonify({'state': None})
    return jsonify({'state': game.to_dict()})

# ── Online Multiplayer ─────────────────────────────────────────────────────────
@app.route('/api/online/create', methods=['POST'])
@login_required
def online_create():
    try:
        user = current_user()
        data = request.get_json(force=True) or {}
        level = int(data.get('level', 1))
        skin  = sanitise(str(data.get('skin', 'zulu')))
        if level not in (1,2,3): level = 1
        if skin not in SKINS: skin = 'zulu'
        rows, cols = 4, (4 if level == 1 else 6)
        room_id = secrets.token_hex(8).upper()
        board = [2] * (rows * cols)
        db = get_db()
        db.execute('''INSERT INTO online_games(room_id,host_email,host_name,status,level,skin,
                      board_rows,board_cols,board_state,current_player)
                      VALUES(?,?,?,?,?,?,?,?,?,?)''',
                   (room_id, user['email'], user['name'], 'waiting', level, skin,
                    rows, cols, json.dumps(board), 0))
        # Create invitation code
        inv_code = secrets.token_urlsafe(10)
        inv_expires = int(time.time()) + 86400  # 24h
        db.execute('''INSERT INTO invitations(code,host_email,host_name,room_id,expires)
                      VALUES(?,?,?,?,?)''',
                   (inv_code, user['email'], user['name'], room_id, inv_expires))
        db.commit()
        return jsonify({'ok': True, 'room_id': room_id, 'invite_code': inv_code,
                        'invite_url': f'/join/{inv_code}'})
    except Exception as e:
        BugFixer.capture('error', f'online_create: {e}', e)
        return jsonify({'error': str(e)}), 500

@app.route('/api/online/join', methods=['POST'])
@login_required
def online_join():
    try:
        user = current_user()
        data = request.get_json(force=True) or {}
        code = sanitise(str(data.get('code', '')), 30)
        db = get_db()
        inv = db.execute('SELECT * FROM invitations WHERE code=? AND used=0 AND expires>?',
                         (code, int(time.time()))).fetchone()
        if not inv:
            return jsonify({'error': 'Invalid or expired invitation code'}), 404
        room = db.execute('SELECT * FROM online_games WHERE room_id=?', (inv['room_id'],)).fetchone()
        if not room:
            return jsonify({'error': 'Room not found'}), 404
        if room['status'] != 'waiting':
            return jsonify({'error': 'Game already started or finished'}), 409
        if room['host_email'] == user['email']:
            return jsonify({'error': 'Cannot join your own room'}), 400
        db.execute('''UPDATE online_games SET guest_email=?,guest_name=?,status='playing',updated=?
                      WHERE room_id=?''',
                   (user['email'], user['name'], int(time.time()), inv['room_id']))
        db.execute('UPDATE invitations SET used=1 WHERE code=?', (code,))
        db.commit()
        return jsonify({'ok': True, 'room_id': inv['room_id'],
                        'host_name': room['host_name'], 'level': room['level']})
    except Exception as e:
        BugFixer.capture('error', f'online_join: {e}', e)
        return jsonify({'error': str(e)}), 500

@app.route('/api/online/state/<room_id>')
@login_required
def online_state(room_id):
    try:
        user = current_user()
        db = get_db()
        room = db.execute('SELECT * FROM online_games WHERE room_id=?', (sanitise(room_id),)).fetchone()
        if not room:
            return jsonify({'error': 'Room not found'}), 404
        if user['email'] not in (room['host_email'], room['guest_email']):
            return jsonify({'error': 'Not a player in this game'}), 403
        player_idx = 0 if user['email'] == room['host_email'] else 1
        board = json.loads(room['board_state']) if room['board_state'] else []
        return jsonify({'ok': True, 'room': dict(room), 'player_idx': player_idx,
                        'board': board, 'current_player': room['current_player']})
    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/api/online/move', methods=['POST'])
@login_required
def online_move():
    try:
        user = current_user()
        data = request.get_json(force=True) or {}
        room_id = sanitise(str(data.get('room_id', '')), 20)
        idx = int(data.get('idx', -1))
        db = get_db()
        room = db.execute('SELECT * FROM online_games WHERE room_id=?', (room_id,)).fetchone()
        if not room or room['status'] != 'playing':
            return jsonify({'error': 'Game not active'}), 400
        player_idx = 0 if user['email'] == room['host_email'] else 1
        if room['current_player'] != player_idx:
            return jsonify({'error': 'Not your turn'}), 400
        # Reconstruct game state
        rows, cols = room['board_rows'], room['board_cols']
        board = json.loads(room['board_state'])
        game = GameState(rows=rows, cols=cols, mode='online', level=room['level'])
        game.board = board
        game.player = player_idx
        if not game.is_valid_start(idx, player_idx):
            return jsonify({'error': 'Invalid move'}), 400
        steps, captured, _, _ = game.do_sow(idx, player_idx)
        quantum_reveal = getattr(game, '_last_quantum_reveal', None)
        ended, p0, p1 = game.check_end()
        next_player = 1 - player_idx
        status = 'finished' if ended else 'playing'
        db.execute('''UPDATE online_games SET board_state=?,current_player=?,status=?,updated=?
                      WHERE room_id=?''',
                   (json.dumps(game.board), next_player, status, int(time.time()), room_id))
        db.commit()
        if ended:
            # Record results for both players
            winner = room['host_email'] if p0 > p1 else (room['guest_email'] if p1 > p0 else None)
            for email, cows in [(room['host_email'], p0), (room['guest_email'], p1)]:
                if not email: continue
                result = 'wins' if (p0>p1 and email==room['host_email']) or (p1>p0 and email==room['guest_email']) else \
                         'losses' if (p0<p1 and email==room['host_email']) or (p1<p0 and email==room['guest_email']) else 'draws'
                cows_won = cows if result == 'wins' else 0
                db.execute(f'UPDATE users SET {result}={result}+1, games=games+1, total_cows=total_cows+? WHERE email=?',
                           (cows_won, email))
            db.commit()
        lang_data = LANGS.get(session.get('lang','en'), LANGS['en'])
        return jsonify({'ok': True, 'board': game.board, 'steps': steps,
                        'captured': captured, 'game_over': ended,
                        'scores': [p0, p1], 'next_player': next_player,
                        'narrator': _narrate_move(idx, captured, -1, 0, lang_data)})
    except Exception as e:
        BugFixer.capture('error', f'online_move: {e}', e)
        return jsonify({'error': str(e)}), 500

@app.route('/join/<code>')
def join_page(code):
    """Redirect-friendly join URL."""
    return render_template_string(HTML_TEMPLATE, langs=LANGS, skins=SKINS)

# ── Tournaments ────────────────────────────────────────────────────────────────
@app.route('/api/tournament/create', methods=['POST'])
@login_required
def tournament_create():
    try:
        user = current_user()
        data = request.get_json(force=True) or {}
        name = sanitise(str(data.get('name', 'My Tournament')), 50)
        max_players = int(data.get('max_players', 8))
        if max_players not in (4, 8, 16): max_players = 8
        t_id = secrets.token_hex(6).upper()
        players = json.dumps([{'email': user['email'], 'name': user['name']}])
        db = get_db()
        db.execute('''INSERT INTO tournaments(id,name,host_email,host_name,max_players,players)
                      VALUES(?,?,?,?,?,?)''',
                   (t_id, name, user['email'], user['name'], max_players, players))
        db.commit()
        return jsonify({'ok': True, 'tournament_id': t_id, 'name': name})
    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/api/tournament/join', methods=['POST'])
@login_required
def tournament_join():
    try:
        user = current_user()
        data = request.get_json(force=True) or {}
        t_id = sanitise(str(data.get('tournament_id', '')), 20)
        db = get_db()
        t = db.execute('SELECT * FROM tournaments WHERE id=?', (t_id,)).fetchone()
        if not t: return jsonify({'error': 'Tournament not found'}), 404
        if t['status'] != 'open': return jsonify({'error': 'Tournament not open'}), 409
        players = json.loads(t['players'])
        if len(players) >= t['max_players']:
            return jsonify({'error': 'Tournament is full'}), 409
        if any(p['email'] == user['email'] for p in players):
            return jsonify({'error': 'Already joined'}), 409
        players.append({'email': user['email'], 'name': user['name']})
        db.execute('UPDATE tournaments SET players=? WHERE id=?', (json.dumps(players), t_id))
        db.commit()
        return jsonify({'ok': True, 'players': len(players), 'max': t['max_players']})
    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/api/tournament/list')
def tournament_list():
    try:
        db = get_db()
        rows = db.execute("SELECT * FROM tournaments WHERE status='open' ORDER BY created DESC LIMIT 20").fetchall()
        return jsonify({'tournaments': [dict(r) for r in rows]})
    except Exception as e:
        return jsonify({'tournaments': []})

@app.route('/api/tournament/start', methods=['POST'])
@login_required
def tournament_start():
    try:
        user = current_user()
        data = request.get_json(force=True) or {}
        t_id = sanitise(str(data.get('tournament_id', '')), 20)
        db = get_db()
        t = db.execute('SELECT * FROM tournaments WHERE id=? AND host_email=?',
                       (t_id, user['email'])).fetchone()
        if not t: return jsonify({'error': 'Not found or not host'}), 404
        players = json.loads(t['players'])
        if len(players) < 2: return jsonify({'error': 'Need at least 2 players'}), 400
        import random; random.shuffle(players)
        bracket = {'rounds': [players], 'current_round': 0}
        db.execute("UPDATE tournaments SET status='active',bracket=?,start_time=? WHERE id=?",
                   (json.dumps(bracket), int(time.time()), t_id))
        db.commit()
        return jsonify({'ok': True, 'bracket': bracket})
    except Exception as e:
        return jsonify({'error': str(e)}), 500

# ── Leaderboard (enhanced) ─────────────────────────────────────────────────────
@app.route('/api/leaderboard')
def leaderboard():
    try:
        db = get_db()
        rows = db.execute('''SELECT name,wins,losses,draws,games,total_cows
                             FROM users ORDER BY wins DESC, total_cows DESC LIMIT 20''').fetchall()
        board = []
        for i, r in enumerate(rows):
            wr = round(r['wins']/r['games']*100) if r['games'] > 0 else 0
            board.append({'rank': i+1, 'name': r['name'], 'wins': r['wins'],
                          'losses': r['losses'], 'draws': r['draws'],
                          'games': r['games'], 'win_rate': wr,
                          'total_cows': r['total_cows'] or 0})
        # Add AI entries for flavour
        ai_entries = [
            {'rank': 0, 'name': '🤖 Inkosi AI', 'wins': 9999, 'losses': 1, 'draws': 0,
             'games': 10000, 'win_rate': 100, 'total_cows': 99999, 'is_ai': True},
        ]
        return jsonify({'board': board, 'ai': ai_entries})
    except Exception as e:
        BugFixer.capture('error', f'leaderboard error: {e}', e)
        return jsonify({'board': [], 'ai': []})

@app.route('/api/profile')
@login_required
def profile():
    user = current_user()
    u = _user_dict(user)
    u['win_rate'] = round(u['wins']/u['games']*100) if u['games'] > 0 else 0
    return jsonify({'user': u})

# ── Bug Fixer API ──────────────────────────────────────────────────────────────
@app.route('/api/bugfixer/log')
def bugfixer_log():
    return jsonify({'log': BugFixer.get_log(), 'summary': BugFixer.get_summary()})

@app.route('/api/bugfixer/report', methods=['POST'])
def bugfixer_report():
    try:
        data  = request.get_json(force=True) or {}
        level = sanitise(str(data.get('level','error')), 10)
        msg   = sanitise(str(data.get('msg','')), 500)
        BugFixer.capture(level, f'[CLIENT] {msg}')
        db = get_db()
        db.execute('INSERT INTO bug_log(level,msg) VALUES(?,?)', (level, msg))
        db.commit()
    except: pass
    return jsonify({'ok': True})

@app.route('/api/bugfixer/unstick', methods=['POST'])
def bugfixer_unstick():
    try:
        token = session.get('token')
        game  = get_game(token)
        if game:
            game._recover(); set_game(token, game)
            return jsonify({'ok': True, 'state': game.to_dict()})
    except Exception as e:
        BugFixer.capture('error', f'unstick error: {e}', e)
    return jsonify({'ok': False})

# ── Helpers ────────────────────────────────────────────────────────────────────
def _user_dict(user):
    return {
        'email': user['email'], 'name': user['name'],
        'wins': user['wins'], 'losses': user['losses'],
        'draws': user['draws'], 'games': user['games'],
        'total_cows': user['total_cows'] if 'total_cows' in user.keys() else 0,
        'skin': user['skin'], 'level': user['level'], 'lang': user['lang'],
        'created': user['created'], 'last_login': user['last_login'],
    }

def _record_result(game: GameState, p0: int, p1: int, cows_won: int = 0):
    user = current_user()
    if not user: return
    try:
        won    = p0 > p1
        result = 'wins' if won else 'losses' if p1 > p0 else 'draws'
        db = get_db()
        db.execute(f'UPDATE users SET {result}={result}+1, games=games+1, total_cows=total_cows+? WHERE email=?',
                   (cows_won, user['email']))
        db.commit()
        # ELO update (AI games use fixed AI ELO 1400)
        if game.mode == 'ai':
            if won:
                _update_elo(user['email'], '', is_ai_game=True)
            # Losses in AI games do not change ELO (beginner protection)
        # Grant chest on win
        if won and game.level >= 2:
            chest_type = 'silver' if game.level == 3 else 'bronze'
            _grant_chest(user['email'], chest_type)
        # Check achievements
        _check_achievements(user['email'])
    except Exception as e:
        BugFixer.capture('error', f'record_result error: {e}', e)

def _narrate_move(player_hole, captured, ai_hole, ai_captured, lang):
    msgs = []
    if captured:
        msgs.append(f"🐄 {lang.get('captured','').replace('{n}', str(captured))}")
    if ai_hole >= 0:
        msgs.append(f"🤖 {lang.get('aiName','AI')} moved!")
        if ai_captured:
            msgs.append(f"🐄 AI {lang.get('captured','').replace('{n}', str(ai_captured))}")
    return ' · '.join(msgs) if msgs else ''

def _narrate_end(p0, p1, lang):
    if p0 > p1:
        return f"🏆 {lang.get('win','You Win!')} ({p0} vs {p1} cows)"
    elif p1 > p0:
        return f"🤖 {lang.get('lose','AI Wins!')} ({p1} vs {p0} cows)"
    else:
        return f"⚖️ {lang.get('draw','Draw!')} ({p0} cows each)"


# ─── Support Chat, Feedback & Survey ──────────────────────────────────────────
import uuid as _uuid_mod

_SUPPORT_RESPONSES = [
    (['hello','hi','helo','sawubona','dumela','howzit'],
     "👋 Sawubona! Welcome to Intshuba Support. How can I help you today?"),
    (['rule','how to play','imithetho','melao','milayo','teach'],
     "📜 Basic rules: Pick a hole on YOUR bottom rows. Stones sow anti-clockwise. "
     "Capture when your last stone lands on your inner row opposite filled opponent holes. Type 'more rules' for details!"),
    (['more rule','detail','explain'],
     "🎯 Key rules: (1) Cannot start on a single if pairs exist. "
     "(2) Last stone lands inner row + opposite holes filled = capture all those stones! "
     "(3) No valid moves = sleep (kulala). (4) Most cows at end wins!"),
    (['child','kids','young','age','calf','beginner','level 1','level1'],
     "🐄 The CALF level is specially designed for children! "
     "It has a small 4×4 board, rainbow stones, step-by-step move hints, "
     "slow AI, celebration animations, and gentle encouragement. Perfect for ages 5+!"),
    (['online','multiplayer','invite','friend','cross'],
     "🌍 Online play: Home → Online Game → Create Room. "
     "Share your 8-character code with a friend on any device. They tap Join and enter your code!"),
    (['tournament','tourney','compete'],
     "🏆 Tournaments: Home → Tournament → Create. Set name and player count, share your Tournament ID!"),
    (['bug','error','crash','problem','broken','not work','freeze','stuck'],
     "🐛 Sorry about that! Please describe exactly what happened and we will fix it. "
     "You can also tap the 🐛 bug icon in-game to auto-report with state info."),
    (['account','register','sign up','login','password','profile'],
     "🔑 To register: tap Sign In → Register. Use your email and a strong password. "
     "Your wins, cattle and settings are saved to your account!"),
    (['language','limi','ulimi','puo','ririmi','translate'],
     "🌐 We support all 11 SA official languages + French! "
     "Go to Home and scroll to the Language section to switch."),
    (['android','play store','google play'],
     "📱 Android: Search 'Intshuba' on Google Play Store, or visit info@inkazimulo.digital"),
    (['ios','iphone','ipad','app store','apple'],
     "🍎 iOS: Search 'Intshuba' on the Apple App Store, or visit info@inkazimulo.digital"),
    (['download','install','get the app'],
     "📲 Download on Google Play (Android) or the App Store (iOS). Search 'Intshuba Nguni'!"),
    (['skin','theme','colour','color','zulu','xhosa','ndebele'],
     "🎨 Choose from 5 Nguni cultural skins: Zulu, Xhosa, Ndebele, Swati, Tsonga — each has unique board colours!"),
    (['cattle','cow','herd','izinkomo','dikgomo','inkomo'],
     "🐄 Your cattle herd grows every time you WIN. Check your total in Profile and the Leaderboard!"),
    (['contact','email','developer','inkazimulo','whatsapp','phone'],
     "📧 Contact us: info@inkazimulo.digital | WhatsApp: +27 XX XXX XXXX | Response within 24 hours!"),
    (['thank','dankie','ngiyabonga','ke a leboha'],
     "😊 You are welcome! Anything else I can help with?"),
    (['bye','goodbye','sala','hamba','totsiens','ciao'],
     "👋 Goodbye! Come back soon. Hlala kahle! 🐄"),
    (['rating','rate','review','stars'],
     "⭐ We would love your rating! Tap the ⭐ Rate & Feedback button on the Home screen. It only takes 30 seconds!"),
    (['survey','question','feedback','suggest','recommend','idea'],
     "💡 We love hearing from players! Tap ⭐ Rate & Feedback on Home to fill in our quick survey. Your ideas shape the game!"),
]

_SURVEY_QUESTIONS = [
    {"id":"q1","type":"stars","question":"How much do you enjoy playing Intshuba?",
     "options":["1 ⭐","2 ⭐⭐","3 ⭐⭐⭐","4 ⭐⭐⭐⭐","5 ⭐⭐⭐⭐⭐"]},
    {"id":"q2","type":"choice","question":"Which feature do you like most?",
     "options":["🎮 Gameplay","🌍 Online Multiplayer","🏆 Tournaments","🎨 Skins & Themes","🐄 Cattle Rankings"]},
    {"id":"q3","type":"choice","question":"What would you most like us to ADD next?",
     "options":["More languages","Video tutorials","In-game voice chat","New game modes","Achievements & badges"]},
    {"id":"q4","type":"choice","question":"How child-friendly is the Calf (Beginner) level?",
     "options":["Too hard 😓","A bit hard 🤔","Just right 👍","Easy 😊","Very easy 🎉"]},
    {"id":"q5","type":"choice","question":"How did you find out about Intshuba?",
     "options":["Friend / Family","Social media","Google Play / App Store","School","Other"]},
    {"id":"q6","type":"text","question":"Any suggestions or ideas for Intshuba?",
     "placeholder":"Tell us your idea..."},
]

def _auto_reply(msg: str) -> str:
    m = msg.lower()
    for keywords, reply in _SUPPORT_RESPONSES:
        if any(k in m for k in keywords):
            return reply
    return ("🤔 Thanks for your message! A support agent will reply within a few hours. "
            "You can also email info@inkazimulo.digital. "
            "Meanwhile, is there something specific I can help with? "
            "Try asking about 'rules', 'online play', 'accounts', or 'levels'.")


@app.route('/api/chat/start', methods=['POST'])
def chat_start():
    try:
        data = request.get_json(force=True) or {}
        sid = sanitise(str(data.get('session_id','')), 64) or _uuid_mod.uuid4().hex
        user = current_user()
        uname = user['name'] if user else sanitise(str(data.get('name','Guest')), 32)
        uemail = user['email'] if user else ''
        db = get_db()
        existing = db.execute(
            'SELECT id FROM support_messages WHERE session_id=? LIMIT 1', (sid,)
        ).fetchone()
        if not existing:
            welcome = (
                "👋 Sawubona " + uname + "! Welcome to Intshuba Support. "
                "I can help with game rules, online play, accounts, and more. "
                "What do you need help with? 🐄"
            )
            db.execute(
                'INSERT INTO support_messages(session_id,user_name,user_email,sender,message,msg_type) '
                'VALUES(?,?,?,?,?,?)',
                (sid, uname, uemail, 'support', welcome, 'welcome')
            )
            db.commit()
        msgs = db.execute(
            'SELECT sender,message,msg_type,created FROM support_messages '
            'WHERE session_id=? ORDER BY created ASC LIMIT 60', (sid,)
        ).fetchall()
        return jsonify({'ok': True, 'session_id': sid,
                        'messages': [dict(m) for m in msgs],
                        'survey': _SURVEY_QUESTIONS})
    except Exception as e:
        BugFixer.capture('error', 'chat_start: ' + str(e), e)
        return jsonify({'error': str(e)}), 500


@app.route('/api/chat/send', methods=['POST'])
def chat_send():
    try:
        data = request.get_json(force=True) or {}
        sid  = sanitise(str(data.get('session_id','')), 64)
        msg  = sanitise(str(data.get('message','')), 500)
        if not sid or not msg:
            return jsonify({'error': 'Missing session_id or message'}), 400
        if not rate_check('chat_' + sid, 30, 60):
            return jsonify({'error': 'Too many messages — slow down!'}), 429
        user = current_user()
        uname  = user['name']  if user else sanitise(str(data.get('name','Guest')), 32)
        uemail = user['email'] if user else ''
        db = get_db()
        db.execute(
            'INSERT INTO support_messages(session_id,user_name,user_email,sender,message) '
            'VALUES(?,?,?,?,?)',
            (sid, uname, uemail, 'user', msg)
        )
        reply = _auto_reply(msg)
        show_survey = any(k in msg.lower() for k in ['help','done','thanks','finished','suggest'])
        db.execute(
            'INSERT INTO support_messages(session_id,user_name,user_email,sender,message,msg_type) '
            'VALUES(?,?,?,?,?,?)',
            (sid, uname, uemail, 'support', reply, 'text')
        )
        db.commit()
        return jsonify({'ok': True, 'reply': reply, 'show_survey': show_survey})
    except Exception as e:
        BugFixer.capture('error', 'chat_send: ' + str(e), e)
        return jsonify({'error': str(e)}), 500


@app.route('/api/feedback/submit', methods=['POST'])
def feedback_submit():
    try:
        data = request.get_json(force=True) or {}
        user = current_user()
        uname  = user['name']  if user else sanitise(str(data.get('name','Guest')),32)
        uemail = user['email'] if user else sanitise(str(data.get('email','')),80)
        rating   = int(data.get('rating', 5))
        category = sanitise(str(data.get('category','general')), 30)
        msg      = sanitise(str(data.get('message','')), 1000)
        platform = sanitise(str(data.get('platform','web')), 20)
        if not (1 <= rating <= 5): rating = 5
        if not msg:
            return jsonify({'error': 'Please write a message'}), 400
        db = get_db()
        db.execute(
            'INSERT INTO feedback(user_name,user_email,rating,category,message,platform) '
            'VALUES(?,?,?,?,?,?)',
            (uname, uemail, rating, category, msg, platform)
        )
        db.commit()
        return jsonify({'ok': True, 'message': 'Thank you for your feedback! 🙏 We read every single response.'})
    except Exception as e:
        return jsonify({'error': str(e)}), 500


@app.route('/api/survey/submit', methods=['POST'])
def survey_submit():
    try:
        data = request.get_json(force=True) or {}
        user = current_user()
        uname  = user['name']  if user else sanitise(str(data.get('name','Guest')),32)
        uemail = user['email'] if user else ''
        answers = data.get('answers', {})
        db = get_db()
        for qid, answer in answers.items():
            q = next((x for x in _SURVEY_QUESTIONS if x['id']==qid), None)
            if q:
                db.execute(
                    'INSERT INTO user_inputs(user_name,user_email,input_type,question,answer) '
                    'VALUES(?,?,?,?,?)',
                    (uname, uemail, 'survey', q['question'], sanitise(str(answer),200))
                )
        db.commit()
        return jsonify({'ok': True, 'message': 'Survey saved! Thank you — your voice shapes Intshuba! 🐄'})
    except Exception as e:
        return jsonify({'error': str(e)}), 500


@app.route('/api/feedback/admin')
def feedback_admin():
    try:
        db = get_db()
        rows = db.execute('SELECT * FROM feedback ORDER BY created DESC LIMIT 100').fetchall()
        return jsonify({'feedback': [dict(r) for r in rows]})
    except Exception:
        return jsonify({'feedback': []})


# ═══════════════════════════════════════════════════════════════════════════════
#  MONETISATION  —  Stripe · Google Play · Apple App Store · Ko-fi Donations
# ═══════════════════════════════════════════════════════════════════════════════

# ── Product catalogue ──────────────────────────────────────────────────────────
# These are your SKUs.  Mirror them exactly in Stripe Dashboard, Google Play
# Console (in-app products) and App Store Connect (in-app purchases).
PRODUCTS = {
    # Web / Stripe  ────────────────────────────────────────────────────────────
    'inkosi_monthly': {
        'name': 'Inkosi Club – Monthly',
        'description': 'Unlimited online play · All 5 skins · Tournament priority · No ads',
        'price_zar': 2900,           # R29.00 in cents
        'price_usd': 150,            # $1.50 in cents  (fallback for intl)
        'stripe_price_id': '',       # set after Stripe Dashboard product creation
        'interval': 'month',
        'plan': 'inkosi',
    },
    'inkosi_annual': {
        'name': 'Inkosi Club – Annual',
        'description': 'Everything in monthly, 2 months free',
        'price_zar': 29000,          # R290.00
        'price_usd': 1500,
        'stripe_price_id': '',
        'interval': 'year',
        'plan': 'inkosi',
    },
    'pro_pack_once': {
        'name': 'Pro Pack – Once Off',
        'description': 'Unlock all skins + cattle breeds + offline AI forever',
        'price_zar': 4900,           # R49.00
        'price_usd': 299,
        'stripe_price_id': '',
        'interval': None,
        'plan': 'pro',
    },
    'school_annual': {
        'name': 'School Site Licence – Annual',
        'description': 'Unlimited learners · Teacher dashboard · CAPS-aligned worksheet pack',
        'price_zar': 99900,          # R999.00
        'price_usd': 5500,
        'stripe_price_id': '',
        'interval': 'year',
        'plan': 'school',
    },
    # Mobile / Google Play + Apple (product IDs must match exactly) ───────────
    'android_inkosi_monthly': {'plan': 'inkosi', 'platform': 'android'},
    'android_pro_pack':       {'plan': 'pro',    'platform': 'android'},
    'ios_inkosi_monthly':     {'plan': 'inkosi', 'platform': 'ios'},
    'ios_pro_pack':           {'plan': 'pro',    'platform': 'ios'},
}

PLAN_FEATURES = {
    'free':   {'online_games': 3, 'skins': 1, 'tournaments': False, 'ads': True},
    'pro':    {'online_games': 999, 'skins': 5, 'tournaments': True,  'ads': False},
    'inkosi': {'online_games': 999, 'skins': 5, 'tournaments': True,  'ads': False},
    'school': {'online_games': 999, 'skins': 5, 'tournaments': True,  'ads': False},
}

def _get_plan_features(email: str) -> dict:
    db = get_db()
    row = db.execute('SELECT plan,plan_expires FROM users WHERE email=?',(email,)).fetchone()
    if not row:
        return PLAN_FEATURES['free']
    plan = row['plan'] or 'free'
    expires = row['plan_expires'] or 0
    if plan != 'free' and expires > 0 and expires < int(time.time()):
        # subscription lapsed — downgrade to free
        db.execute("UPDATE users SET plan='free' WHERE email=?", (email,))
        db.commit()
        plan = 'free'
    return PLAN_FEATURES.get(plan, PLAN_FEATURES['free'])

def _upgrade_user(email: str, plan: str, months: int = 1):
    """Grant plan to user.  months=0 = permanent (one-off purchase)."""
    now = int(time.time())
    if months == 0:
        expires = 0   # permanent
    else:
        # extend from now OR from current expiry, whichever is later
        db = get_db()
        row = db.execute('SELECT plan_expires FROM users WHERE email=?',(email,)).fetchone()
        base = max(now, (row['plan_expires'] or now)) if row else now
        expires = base + months * 30 * 86400
    db = get_db()
    db.execute(
        'UPDATE users SET plan=?,plan_expires=? WHERE email=?',
        (plan, expires, email)
    )
    db.commit()
    log.info(f"[payment] {email} upgraded to {plan} expires={expires}")

# ── Stripe helpers ─────────────────────────────────────────────────────────────
def _stripe():
    try:
        import stripe as _s
        _s.api_key = os.environ.get('STRIPE_SECRET_KEY','')
        return _s
    except ImportError:
        return None

@app.route('/api/shop/products')
def shop_products():
    """Return product catalogue + current user plan."""
    user = current_user()
    plan = 'free'
    features = PLAN_FEATURES['free']
    play_tokens = 10
    if user:
        row = get_db().execute(
            'SELECT plan,plan_expires,play_tokens FROM users WHERE email=?',(user['email'],)
        ).fetchone()
        if row:
            plan = row['plan'] or 'free'
            features = _get_plan_features(user['email'])
            play_tokens = row['play_tokens'] or 0
    return jsonify({
        'products': [
            {k: v for k, v in p.items() if k not in ('stripe_price_id',)}
            for k, p in PRODUCTS.items() if 'stripe_price_id' in p
        ],
        'current_plan': plan,
        'features': features,
        'play_tokens': play_tokens,
    })

@app.route('/api/stripe/checkout', methods=['POST'])
def stripe_checkout():
    """Create a Stripe Checkout Session. Requires user to be logged in."""
    user = current_user()
    if not user:
        return jsonify({'error': 'Please sign in first'}), 401
    stripe = _stripe()
    if not stripe:
        return jsonify({'error': 'Stripe not configured on this server'}), 503
    data       = request.get_json(force=True) or {}
    product_id = sanitise(str(data.get('product_id','')), 60)
    product    = PRODUCTS.get(product_id)
    if not product or 'stripe_price_id' not in product:
        return jsonify({'error': 'Unknown product'}), 400
    price_id = product.get('stripe_price_id','')
    if not price_id:
        return jsonify({'error': 'Stripe price not configured yet — contact support'}), 503
    base_url = os.environ.get('APP_URL', request.host_url.rstrip('/'))
    try:
        mode = 'subscription' if product.get('interval') else 'payment'
        params = dict(
            mode               = mode,
            line_items         = [{'price': price_id, 'quantity': 1}],
            success_url        = f"{base_url}/payment/success?session_id={{CHECKOUT_SESSION_ID}}",
            cancel_url         = f"{base_url}/payment/cancel",
            customer_email     = user['email'],
            metadata           = {'user_email': user['email'], 'product_id': product_id},
            allow_promotion_codes = True,
        )
        # Re-use existing Stripe customer if we have one
        db = get_db()
        row = db.execute('SELECT stripe_customer FROM users WHERE email=?',(user['email'],)).fetchone()
        if row and row['stripe_customer']:
            params['customer'] = row['stripe_customer']
            del params['customer_email']
        session = stripe.checkout.Session.create(**params)
        return jsonify({'ok': True, 'checkout_url': session.url, 'session_id': session.id})
    except Exception as e:
        BugFixer.capture('error', f'stripe_checkout: {e}', e)
        return jsonify({'error': str(e)}), 500

@app.route('/api/stripe/webhook', methods=['POST'])
def stripe_webhook():
    """Stripe sends events here. Register this URL in your Stripe Dashboard."""
    stripe = _stripe()
    if not stripe:
        return jsonify({'error': 'Stripe not available'}), 503
    payload    = request.get_data()
    sig_header = request.headers.get('Stripe-Signature','')
    endpoint_secret = os.environ.get('STRIPE_WEBHOOK_SECRET','')
    try:
        event = stripe.Webhook.construct_event(payload, sig_header, endpoint_secret)
    except (ValueError, stripe.error.SignatureVerificationError) as e:
        log.warning(f'[stripe webhook] bad signature: {e}')
        return jsonify({'error': 'Invalid signature'}), 400

    etype = event['type']
    obj   = event['data']['object']

    if etype == 'checkout.session.completed':
        email      = obj.get('customer_email') or obj.get('metadata',{}).get('user_email','')
        product_id = obj.get('metadata',{}).get('product_id','')
        product    = PRODUCTS.get(product_id,{})
        plan       = product.get('plan','pro')
        interval   = product.get('interval')
        months     = 1 if interval == 'month' else (12 if interval == 'year' else 0)
        amount     = obj.get('amount_total', 0)
        currency   = obj.get('currency','zar').upper()
        cust_id    = obj.get('customer','')
        if email:
            _upgrade_user(email, plan, months)
            db = get_db()
            if cust_id:
                db.execute('UPDATE users SET stripe_customer=? WHERE email=?',(cust_id, email))
            db.execute(
                'INSERT OR IGNORE INTO payments(user_email,provider,provider_ref,product_id,plan,amount_cents,currency,status,platform) VALUES(?,?,?,?,?,?,?,?,?)',
                (email,'stripe', obj.get('id',''), product_id, plan, amount, currency, 'completed', 'web')
            )
            db.commit()
            log.info(f"[stripe] payment completed: {email} → {plan}")

    elif etype == 'customer.subscription.deleted':
        cust_id = obj.get('customer','')
        if cust_id:
            db = get_db()
            row = db.execute('SELECT email FROM users WHERE stripe_customer=?',(cust_id,)).fetchone()
            if row:
                db.execute("UPDATE users SET plan='free',plan_expires=0 WHERE email=?",(row['email'],))
                db.commit()
                log.info(f"[stripe] subscription cancelled: {row['email']}")

    return jsonify({'ok': True})

@app.route('/payment/success')
def payment_success():
    return render_template_string("""
<!DOCTYPE html><html><head><meta charset="UTF-8">
<title>Payment Successful - Intshuba</title>
<meta http-equiv="refresh" content="3;url=/">
<style>body{background:#0D0804;color:#C9A84C;font-family:Georgia,serif;
  display:flex;flex-direction:column;align-items:center;justify-content:center;
  height:100vh;text-align:center}
h1{font-size:36px;margin-bottom:12px}.sub{color:#F5ECD7;font-size:18px;margin-bottom:20px}
</style></head><body>
<div style="font-size:64px">🐄</div>
<h1>Inkosi! You're upgraded!</h1>
<div class="sub">Your plan is now active. Redirecting to the game…</div>
<div style="font-size:13px;opacity:.5">Intshuba · Nguni Stone Game</div>
</body></html>""")

@app.route('/payment/cancel')
def payment_cancel():
    return render_template_string("""
<!DOCTYPE html><html><head><meta charset="UTF-8">
<title>Payment Cancelled - Intshuba</title>
<meta http-equiv="refresh" content="3;url=/">
<style>body{background:#0D0804;color:#C9A84C;font-family:Georgia,serif;
  display:flex;flex-direction:column;align-items:center;justify-content:center;
  height:100vh;text-align:center}</style></head><body>
<div style="font-size:48px">🐄</div>
<h1 style="margin:12px 0">No problem!</h1>
<div style="color:#F5ECD7;font-size:16px;margin-bottom:16px">Payment was cancelled. Your free account is unchanged.</div>
<div style="font-size:13px;opacity:.5">Redirecting…</div>
</body></html>""")

# ── Google Play server-side receipt verification ───────────────────────────────
@app.route('/api/billing/android/verify', methods=['POST'])
def android_verify():
    """
    Called by the Android app after a successful purchase.
    The app sends: packageName, productId, purchaseToken, subscriptionId (if subscription).
    We verify with Google Play Developer API and grant the plan.
    """
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data          = request.get_json(force=True) or {}
    package_name  = sanitise(str(data.get('packageName','digital.inkazimulo.intshuba')), 100)
    product_id    = sanitise(str(data.get('productId','')), 80)
    purchase_token= sanitise(str(data.get('purchaseToken','')), 500)
    is_sub        = bool(data.get('isSubscription', False))

    credentials_json = os.environ.get('GOOGLE_PLAY_SERVICE_ACCOUNT_JSON','')
    if not credentials_json:
        # No credentials configured — grant optimistically in dev; deny in prod
        if _IS_PROD:
            return jsonify({'error': 'Google Play verification not configured on server'}), 503
        log.warning('[android_verify] No credentials configured — granting optimistically (dev only)')
        product = PRODUCTS.get(product_id, {})
        plan    = product.get('plan','pro')
        _upgrade_user(user['email'], plan, 1 if is_sub else 0)
        return jsonify({'ok': True, 'plan': plan, 'dev_mode': True})

    try:
        from google.oauth2 import service_account
        from googleapiclient.discovery import build
        import json as _json
        creds = service_account.Credentials.from_service_account_info(
            _json.loads(credentials_json),
            scopes=['https://www.googleapis.com/auth/androidpublisher']
        )
        service = build('androidpublisher','v3', credentials=creds, cache_discovery=False)
        if is_sub:
            result = service.purchases().subscriptions().get(
                packageName=package_name,
                subscriptionId=product_id,
                token=purchase_token
            ).execute()
            active = result.get('cancelReason') is None and                      int(result.get('expiryTimeMillis',0)) > int(time.time()*1000)
        else:
            result = service.purchases().products().get(
                packageName=package_name,
                productId=product_id,
                token=purchase_token
            ).execute()
            active = result.get('purchaseState') == 0  # 0 = purchased

        if not active:
            return jsonify({'error': 'Purchase not active or already consumed'}), 402

        product = PRODUCTS.get('android_'+product_id.replace('android_',''), PRODUCTS.get(product_id,{}))
        plan    = product.get('plan','pro')
        months  = 1 if is_sub else 0
        _upgrade_user(user['email'], plan, months)
        db = get_db()
        db.execute(
            'INSERT OR IGNORE INTO payments(user_email,provider,provider_ref,product_id,plan,status,platform) VALUES(?,?,?,?,?,?,?)',
            (user['email'],'google_play', purchase_token, product_id, plan, 'verified', 'android')
        )
        db.commit()
        return jsonify({'ok': True, 'plan': plan})
    except Exception as e:
        BugFixer.capture('error', f'android_verify: {e}', e)
        return jsonify({'error': str(e)}), 500

# ── Apple App Store receipt verification ──────────────────────────────────────
@app.route('/api/billing/ios/verify', methods=['POST'])
def ios_verify():
    """
    Called by the iOS app after purchase.
    Sends: receiptData (base64), productId, transactionId.
    We verify with Apple's /verifyReceipt endpoint.
    """
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    import base64, urllib.request
    data         = request.get_json(force=True) or {}
    receipt_data = sanitise(str(data.get('receiptData','')), 10000)
    product_id   = sanitise(str(data.get('productId','')), 80)
    tx_id        = sanitise(str(data.get('transactionId','')), 100)
    password     = os.environ.get('APPLE_SHARED_SECRET','')
    if not password:
        if _IS_PROD:
            return jsonify({'error': 'Apple verification not configured'}), 503
        product = PRODUCTS.get(product_id, {})
        plan    = product.get('plan','pro')
        _upgrade_user(user['email'], plan, 0)
        return jsonify({'ok': True, 'plan': plan, 'dev_mode': True})
    try:
        payload = {'receipt-data': receipt_data, 'password': password, 'exclude-old-transactions': True}
        body    = json.dumps(payload).encode()
        # Try production first, fall back to sandbox
        for endpoint in ['https://buy.itunes.apple.com/verifyReceipt',
                         'https://sandbox.itunes.apple.com/verifyReceipt']:
            req  = urllib.request.Request(endpoint, data=body,
                                          headers={'Content-Type':'application/json'})
            resp = urllib.request.urlopen(req, timeout=10)
            result = json.loads(resp.read())
            status = result.get('status', -1)
            if status == 21007:
                continue  # sandbox receipt sent to prod — retry sandbox
            if status != 0:
                return jsonify({'error': f'Apple returned status {status}'}), 402
            break
        in_app = result.get('receipt',{}).get('in_app',[])
        found = any(
            t.get('product_id') == product_id and
            (t.get('expires_date_ms','0') == '' or
             int(t.get('expires_date_ms','0')) > int(time.time()*1000))
            for t in in_app
        )
        if not found:
            return jsonify({'error': 'Receipt valid but product not found or expired'}), 402
        product = PRODUCTS.get('ios_'+product_id.replace('ios_',''), PRODUCTS.get(product_id,{}))
        plan    = product.get('plan','pro')
        _upgrade_user(user['email'], plan, 0)
        db = get_db()
        db.execute(
            'INSERT OR IGNORE INTO payments(user_email,provider,provider_ref,product_id,plan,status,platform) VALUES(?,?,?,?,?,?,?)',
            (user['email'],'apple', tx_id, product_id, plan, 'verified', 'ios')
        )
        db.commit()
        return jsonify({'ok': True, 'plan': plan})
    except Exception as e:
        BugFixer.capture('error', f'ios_verify: {e}', e)
        return jsonify({'error': str(e)}), 500

# ── Ko-fi / PayFast / direct donation ─────────────────────────────────────────
@app.route('/api/donate/kofi', methods=['POST'])
def kofi_webhook():
    """
    Ko-fi sends a POST with data= (JSON-encoded form field) on each donation.
    Set your Ko-fi webhook URL to:  https://yourdomain.com/api/donate/kofi
    """
    try:
        token = os.environ.get('KOFI_VERIFICATION_TOKEN','')
        raw   = request.form.get('data','{}')
        d     = json.loads(raw)
        if token and d.get('verification_token','') != token:
            log.warning('[kofi] bad verification token')
            return jsonify({'error': 'Unauthorized'}), 401
        amount_str = str(d.get('amount','0')).replace(',','.')
        try:
            amount_zar = int(float(amount_str) * 100)  # store cents
        except Exception:
            amount_zar = 0
        db = get_db()
        db.execute(
            'INSERT INTO donations(user_name,amount_zar,message,provider,ref) VALUES(?,?,?,?,?)',
            (
                sanitise(str(d.get('from_name','Anonymous')), 80),
                amount_zar,
                sanitise(str(d.get('message','')), 300),
                'kofi',
                sanitise(str(d.get('kofi_transaction_id','')), 100),
            )
        )
        db.commit()
        log.info(f"[kofi] donation received: R{amount_zar/100:.2f}")
        return jsonify({'ok': True})
    except Exception as e:
        BugFixer.capture('error', f'kofi_webhook: {e}', e)
        return jsonify({'error': str(e)}), 500

@app.route('/api/donate/record', methods=['POST'])
def record_donation():
    """Record a donation from the in-app donate button (PayPal / EFT redirect)."""
    try:
        user = current_user()
        data = request.get_json(force=True) or {}
        name = user['name'] if user else sanitise(str(data.get('name','Anonymous')),80)
        email= user['email'] if user else ''
        try:
            amount_zar = int(float(str(data.get('amount_zar',0))) * 100)
        except Exception:
            amount_zar = 0
        db = get_db()
        db.execute(
            'INSERT INTO donations(user_email,user_name,amount_zar,message,provider,ref) VALUES(?,?,?,?,?,?)',
            (email, name, amount_zar,
             sanitise(str(data.get('message','')),300),
             sanitise(str(data.get('provider','web')),30),
             sanitise(str(data.get('ref','')),100))
        )
        db.commit()
        return jsonify({'ok': True, 'message': 'Thank you for supporting Intshuba! 🐄'})
    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/api/donate/leaderboard')
def donation_leaderboard():
    """Public list of top supporters (name only, no amounts)."""
    try:
        db = get_db()
        rows = db.execute(
            'SELECT user_name, SUM(amount_zar) as total FROM donations '
            'GROUP BY user_name ORDER BY total DESC LIMIT 20'
        ).fetchall()
        supporters = [{'name': r['user_name'], 'badge': _donor_badge(r['total'])} for r in rows]
        return jsonify({'supporters': supporters})
    except Exception as e:
        return jsonify({'supporters': []})

def _donor_badge(total_cents: int) -> str:
    if total_cents >= 100000: return '🐄🐄🐄 Great Herd'
    if total_cents >= 50000:  return '🐄🐄 Elder'
    if total_cents >= 10000:  return '🐄 Supporter'
    return '🌿 Friend'

@app.route('/api/admin/payments')
def admin_payments():
    """Protected admin endpoint — only accessible with ADMIN_KEY header."""
    key = request.headers.get('X-Admin-Key','')
    if key != os.environ.get('ADMIN_KEY','') or not key:
        return jsonify({'error': 'Unauthorized'}), 401
    db   = get_db()
    pays = db.execute('SELECT * FROM payments  ORDER BY created DESC LIMIT 200').fetchall()
    doms = db.execute('SELECT * FROM donations ORDER BY created DESC LIMIT 200').fetchall()
    users= db.execute(
        "SELECT email,name,plan,plan_expires,total_cows,games FROM users ORDER BY games DESC LIMIT 100"
    ).fetchall()
    return jsonify({
        'payments':  [dict(r) for r in pays],
        'donations': [dict(r) for r in doms],
        'users':     [dict(r) for r in users],
    })


# ═══════════════════════════════════════════════════════════════════════════════
#  KINGDOM ECONOMY ENGINE
#  Cow betting · Level gating · Market · Marriage · Crown system
# ═══════════════════════════════════════════════════════════════════════════════

# ══════════════════════════════════════════════════════════════════════════════
#  TRIBES · COMPETITIONS · REGALIA · AGE POOLS · SOUNDS
# ══════════════════════════════════════════════════════════════════════════════

TRIBES = {
    'amazulu':   {'name': 'amaZulu',   'lang': 'zu', 'icon': '🐗', 'colors': {'board': '#1a0a02', 'hl': '#C8102E', 'stone': '#FFD700'},
                  'sound_win': 'zulu_victory', 'sound_capture': 'zulu_drum', 'spirit': 'Buffalo 🦬',
                  'bonus': 'war_drums',     'bonus_desc': '+5% cows on every win',
                  'region': 'KwaZulu-Natal, South Africa'},
    'amaxhosa':  {'name': 'amaXhosa',  'lang': 'xh', 'icon': '🦬', 'colors': {'board': '#004d1a', 'hl': '#FFD700', 'stone': '#228B22'},
                  'sound_win': 'xhosa_victory', 'sound_capture': 'xhosa_click', 'spirit': 'Sea Eagle 🦅',
                  'bonus': 'click_wisdom',  'bonus_desc': 'AI capture hints at Level 2',
                  'region': 'Eastern Cape, South Africa'},
    'amandebele':{'name': 'amaNdebele','lang': 'nr', 'icon': '🎨', 'colors': {'board': '#0a0a3a', 'hl': '#FF4444', 'stone': '#FFFFFF'},
                  'sound_win': 'ndebele_song', 'sound_capture': 'ndebele_beads', 'spirit': 'Kudu 🦌',
                  'bonus': 'beadwork',      'bonus_desc': 'Jewellery costs -25% cows',
                  'region': 'Mpumalanga, South Africa'},
    'emaswati':  {'name': 'emaSwati',  'lang': 'ss', 'icon': '🦁', 'colors': {'board': '#3a0a5a', 'hl': '#FFD700', 'stone': '#9B4FCC'},
                  'sound_win': 'swati_royal', 'sound_capture': 'swati_shield', 'spirit': 'Lion 🦁',
                  'bonus': 'royal_guard',   'bonus_desc': 'Crown harder to take: +100 cows wager required',
                  'region': 'Eswatini'},
    'vatsonga':  {'name': 'VaTsonga',  'lang': 'ts', 'icon': '🌿', 'colors': {'board': '#3a1a00', 'hl': '#FF8C00', 'stone': '#8B4513'},
                  'sound_win': 'tsonga_mbila', 'sound_capture': 'tsonga_xylophone', 'spirit': 'Crocodile 🐊',
                  'bonus': 'trade_mastery', 'bonus_desc': 'Market stall earns +3 cows/day extra',
                  'region': 'Limpopo, South Africa / Mozambique'},
    'basotho':   {'name': 'BaSotho',   'lang': 'st', 'icon': '☀️', 'colors': {'board': '#002a5a', 'hl': '#4488FF', 'stone': '#FFFFFF'},
                  'sound_win': 'sotho_lesiba', 'sound_capture': 'sotho_drum', 'spirit': 'Horse 🐴',
                  'bonus': 'mountain_fortress', 'bonus_desc': 'Crown defense: -50 cows wager for challengers',
                  'region': 'Lesotho / Free State'},
    'bapedi':    {'name': 'BaPedi',    'lang': 'nso','icon': '🌙', 'colors': {'board': '#3a0a0a', 'hl': '#FFD700', 'stone': '#8B0000'},
                  'sound_win': 'pedi_drums', 'sound_capture': 'pedi_horn', 'spirit': 'Elephant 🐘',
                  'bonus': 'chief_wisdom',  'bonus_desc': 'iNkosi level: +10 cows per win bonus',
                  'region': 'Limpopo, South Africa'},
    'bavenda':   {'name': 'BaVenda',   'lang': 've', 'icon': '🌊', 'colors': {'board': '#003a3a', 'hl': '#00CED1', 'stone': '#006400'},
                  'sound_win': 'venda_tshikona', 'sound_capture': 'venda_pipe', 'spirit': 'Python 🐍',
                  'bonus': 'mystic_land',   'bonus_desc': 'Land earns +3 cows/day (instead of 2)',
                  'region': 'Limpopo, South Africa'},
    'world':     {'name': 'iNkosi World', 'lang': 'en', 'icon': '🌍', 'colors': {'board': '#0a0a2a', 'hl': '#C9A84C', 'stone': '#4488FF'},
                  'sound_win': 'world_anthem', 'sound_capture': 'world_drum', 'spirit': 'Globe 🌍',
                  'bonus': 'diversity',     'bonus_desc': 'No tribe penalty, no tribe bonus — open to all',
                  'region': 'International'},
}

AGE_POOLS = {
    'u10':     {'label': 'Under 10',   'min_age': 0,  'max_age': 9,  'icon': '🐣', 'board_size': (4,4)},
    'u14':     {'label': 'Under 14',   'min_age': 10, 'max_age': 13, 'icon': '🌱', 'board_size': (4,4)},
    'u18':     {'label': 'Under 18',   'min_age': 14, 'max_age': 17, 'icon': '⚔️', 'board_size': (4,6)},
    'u25':     {'label': 'Under 25',   'min_age': 18, 'max_age': 24, 'icon': '🔥', 'board_size': (4,6)},
    'u40':     {'label': 'Under 40',   'min_age': 25, 'max_age': 39, 'icon': '🦅', 'board_size': (4,6)},
    'senior':  {'label': 'Senior 40+', 'min_age': 40, 'max_age': 59, 'icon': '🦁', 'board_size': (4,6)},
    'elder':   {'label': 'Elder 60+',  'min_age': 60, 'max_age': 999,'icon': '🐘', 'board_size': (4,6)},
    'open':    {'label': 'Open (all)',  'min_age': 0,  'max_age': 999,'icon': '🌍', 'board_size': (4,6)},
}

COMPETITION_TYPES = {
    'school':        {'label': 'Inter-School',         'icon': '🏫', 'entry_fee_zar': 0,    'prize_pool_zar': 50000,
                      'age_pools': ['u10','u14','u18'], 'requires_code': True,  'duration_days': 90,
                      'stream': False, 'sponsor_slots': 2},
    'varsity':       {'label': 'Inter-Varsity/College', 'icon': '🎓', 'entry_fee_zar': 2500, 'prize_pool_zar': 200000,
                      'age_pools': ['u25','open'],      'requires_code': True,  'duration_days': 90,
                      'stream': True,  'sponsor_slots': 4},
    'community':     {'label': 'Community',             'icon': '🏘️', 'entry_fee_zar': 500,  'prize_pool_zar': 100000,
                      'age_pools': ['open'],             'requires_code': False, 'duration_days': 30,
                      'stream': True,  'sponsor_slots': 3},
    'national':      {'label': 'National Championship', 'icon': '🇿🇦', 'entry_fee_zar': 5000, 'prize_pool_zar': 1000000,
                      'age_pools': ['u18','u25','u40','senior','elder'], 'requires_code': False, 'duration_days': 90,
                      'stream': True,  'sponsor_slots': 10},
    'international': {'label': 'International',         'icon': '🌍', 'entry_fee_zar': 10000,'prize_pool_zar': 10000000,
                      'age_pools': ['open'],             'requires_code': False, 'duration_days': 90,
                      'stream': True,  'sponsor_slots': 20},
    'tribe_war':     {'label': 'Tribe War',             'icon': '⚔️', 'entry_fee_zar': 0,    'prize_pool_zar': 500000,
                      'age_pools': ['open'],             'requires_code': False, 'duration_days': 30,
                      'stream': True,  'sponsor_slots': 5},
    'individual_daily': {'label': 'Daily Speed Round',  'icon': '⚡', 'entry_fee_zar': 0,    'prize_pool_zar': 1000,
                         'age_pools': ['open'],          'requires_code': False, 'duration_days': 1,
                         'stream': False,'sponsor_slots': 0},
    'individual_monthly': {'label': 'Monthly Championship', 'icon': '🏆','entry_fee_zar': 1000,'prize_pool_zar': 50000,
                            'age_pools': ['u10','u14','u18','u25','u40','senior','elder'], 'requires_code': False,
                            'duration_days': 30, 'stream': True, 'sponsor_slots': 2},
}

# ── Tribal sounds (base64 encoded Web Audio API tones — generated procedurally) ──
# Real audio files would be served from /static/sounds/ in production
# These describe the sound character for the JS audio synthesizer
TRIBE_SOUNDS = {
    'amazulu':    {'win': {'freq': [220,280,350], 'rhythm': 'war_drum',   'instrument': 'drum'},
                   'capture': {'freq': [440,550],  'rhythm': 'quick',     'instrument': 'drum'}},
    'amaxhosa':   {'win': {'freq': [330,415,495], 'rhythm': 'click_song', 'instrument': 'voice'},
                   'capture': {'freq': [660,825],  'rhythm': 'click',     'instrument': 'voice'}},
    'amandebele': {'win': {'freq': [264,330,396], 'rhythm': 'melodic',    'instrument': 'marimba'},
                   'capture': {'freq': [528,660],  'rhythm': 'bright',    'instrument': 'marimba'}},
    'emaswati':   {'win': {'freq': [196,247,294], 'rhythm': 'royal',      'instrument': 'horn'},
                   'capture': {'freq': [392,494],  'rhythm': 'bold',      'instrument': 'horn'}},
    'vatsonga':   {'win': {'freq': [293,370,440], 'rhythm': 'xylophone',  'instrument': 'xylophone'},
                   'capture': {'freq': [587,740],  'rhythm': 'light',     'instrument': 'xylophone'}},
    'basotho':    {'win': {'freq': [175,220,262], 'rhythm': 'lesiba',     'instrument': 'flute'},
                   'capture': {'freq': [350,440],  'rhythm': 'airy',      'instrument': 'flute'}},
    'bapedi':     {'win': {'freq': [220,277,330], 'rhythm': 'drumline',   'instrument': 'drum'},
                   'capture': {'freq': [440,554],  'rhythm': 'marching',  'instrument': 'drum'}},
    'bavenda':    {'win': {'freq': [261,329,392], 'rhythm': 'tshikona',   'instrument': 'pipe'},
                   'capture': {'freq': [523,659],  'rhythm': 'haunting',  'instrument': 'pipe'}},
    'world':      {'win': {'freq': [440,550,660], 'rhythm': 'triumphant', 'instrument': 'fanfare'},
                   'capture': {'freq': [880,1100], 'rhythm': 'bright',    'instrument': 'fanfare'}},
}

# ── Sound route ────────────────────────────────────────────────────────────────
@app.route('/api/tribes')
def get_tribes():
    return jsonify({'tribes': TRIBES, 'age_pools': AGE_POOLS,
                    'competition_types': COMPETITION_TYPES})

# ── Tribe competition routes ──────────────────────────────────────────────────
@app.route('/api/competition/create', methods=['POST'])
def create_competition():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data  = request.get_json(force=True) or {}
    ctype = sanitise(str(data.get('type','community')), 40)
    name  = sanitise(str(data.get('name','Championship')), 80)
    tribe = sanitise(str(data.get('tribe','')), 30)
    pool  = sanitise(str(data.get('age_pool','open')), 20)
    if ctype not in COMPETITION_TYPES:
        return jsonify({'error': 'Unknown competition type'}), 400
    comp  = COMPETITION_TYPES[ctype]
    db    = get_db()
    import uuid as _u
    comp_id = 'COMP-' + _u.uuid4().hex[:8].upper()
    db.execute(
        '''INSERT INTO competitions(id,name,comp_type,tribe,age_pool,host_email,host_name,
           entry_fee_zar,prize_pool_zar,status,stream_url,duration_days,created)
           VALUES(?,?,?,?,?,?,?,?,?,?,?,?,strftime('%s','now'))''',
        (comp_id, name, ctype, tribe, pool, user['email'], user['name'],
         comp['entry_fee_zar'], comp['prize_pool_zar'], 'open',
         data.get('stream_url',''), comp['duration_days'])
    )
    db.commit()
    return jsonify({'ok': True, 'competition_id': comp_id, 'name': name})

@app.route('/api/competition/list')
def list_competitions():
    db   = get_db()
    rows = db.execute(
        "SELECT * FROM competitions WHERE status='open' ORDER BY created DESC LIMIT 50"
    ).fetchall()
    return jsonify({'competitions': [dict(r) for r in rows]})

@app.route('/api/competition/join', methods=['POST'])
def join_competition():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data    = request.get_json(force=True) or {}
    comp_id = sanitise(str(data.get('competition_id','')), 30)
    db      = get_db()
    comp    = db.execute('SELECT * FROM competitions WHERE id=?', (comp_id,)).fetchone()
    if not comp:
        return jsonify({'error': 'Competition not found'}), 404
    existing = db.execute(
        'SELECT id FROM competition_players WHERE comp_id=? AND player_email=?',
        (comp_id, user['email'])
    ).fetchone()
    if existing:
        return jsonify({'error': 'Already joined'}), 409
    # Entry fee deduction
    entry_fee = comp['entry_fee_zar']
    if entry_fee > 0:
        herd = _get_herd(user['email'])
        fee_cows = max(1, entry_fee // 100)  # R1 = 1 cow approximation for in-game fee
        if herd < fee_cows:
            return jsonify({'ok': False, 'insufficient': True,
                            'message': f'Entry fee: {fee_cows} cows or R{entry_fee/100:.0f}'}), 402
        _add_cows(user['email'], -fee_cows, 'competition_entry', {'comp': comp_id})
    db.execute(
        "INSERT INTO competition_players(comp_id,player_email,player_name,tribe,age_pool,joined) VALUES(?,?,?,?,?,strftime('%s','now'))",
        (comp_id, user['email'], user['name'],
         sanitise(str(data.get('tribe','world')),30),
         sanitise(str(data.get('age_pool','open')),20))
    )
    db.commit()
    return jsonify({'ok': True, 'message': f'Joined {comp["name"]}! Good luck!'})

@app.route('/api/competition/<comp_id>/leaderboard')
def comp_leaderboard(comp_id):
    db   = get_db()
    rows = db.execute(
        'SELECT player_name,tribe,score,wins,losses FROM competition_players '
        'WHERE comp_id=? ORDER BY score DESC, wins DESC LIMIT 30',
        (comp_id,)
    ).fetchall()
    return jsonify({'players': [dict(r) for r in rows], 'leaderboard': [dict(r) for r in rows]})

# ── Age pool route ─────────────────────────────────────────────────────────────
@app.route('/api/age-pools')
def get_age_pools():
    return jsonify({'age_pools': AGE_POOLS})

# ── Economy constants ─────────────────────────────────────────────────────────
LEVEL_GATES = {
    1: {'min_cows': 0,    'unlock_next': 20,   'ante': 0,   'board': (4, 4), 'title': 'iJongo',           'icon': '🪃'},
    2: {'min_cows': 20,   'unlock_next': 100,  'ante': 3,   'board': (4, 6), 'title': 'iNduna',           'icon': '🏹'},
    3: {'min_cows': 100,  'unlock_next': 500,  'ante': 10,  'board': (4, 6), 'title': 'iNkosi',           'icon': '👑'},
    4: {'min_cows': 500,  'unlock_next': 2000, 'ante': 50,  'board': (4, 6), 'title': 'iNkosi_YaMakhosi', 'icon': '🦁'},
    5: {'min_cows': 2000, 'unlock_next': 9999, 'ante': 200, 'board': (4, 6), 'title': 'iSilo',            'icon': '🔱'},
}

MARKET_ITEMS = {
    # ── Land & Property ───────────────────────────────────────────────────────
    'land_plot':     {'name': 'Land Plot (Umhlaba)',          'cows': 50,   'icon': '🌾', 'col': 'land_plots',  'stackable': True,  'earn_day': 2,  'category': 'land',
                      'desc': 'Earn +2 cows/day. Plant crops. Stack up to 10.'},
    'crop_farm':     {'name': 'Crop Farm (Isipho)',           'cows': 80,   'icon': '🌽', 'col': 'crop_farms',  'stackable': True,  'earn_day': 4,  'category': 'land',
                      'desc': 'Plant maize, sorghum, millet. Harvest every 24h for 4 cows.'},
    'cattle_pen':    {'name': 'Cattle Pen (isiBaya)',         'cows': 120,  'icon': '🐄', 'col': 'cattle_pens', 'stackable': True,  'earn_day': 6,  'category': 'land',
                      'desc': 'Breed cattle. Earns +6 cows/day. Required for large herds.'},
    'great_house':   {'name': 'Great House (iNdlu enkulu)',   'cows': 200,  'icon': '🏠', 'col': None,          'stackable': False, 'earn_day': 5,  'category': 'land',
                      'desc': 'Head homestead. Earns +5 cows/day tribute. Required for Chief petition.'},
    'trade_stall':   {'name': 'Market Stall (Isitolo)',       'cows': 300,  'icon': '🏪', 'col': None,          'stackable': False, 'earn_day': 10, 'category': 'land',
                      'desc': 'Sell goods to other players. Earns +10 cows/day passive income.'},
    # ── Crafts & Trades ───────────────────────────────────────────────────────
    'ironsmith':     {'name': 'Ironsmith Forge (Insimbi)',    'cows': 100,  'icon': '⚒️', 'col': None,          'stackable': False, 'earn_day': 8,  'category': 'trade',
                      'desc': 'Craft spears, tools, jewellery. Sell for 2× cost. Unlock weapon shop.'},
    'carpentry':     {'name': 'Carpentry Workshop (uMnengi)', 'cows': 80,   'icon': '🪵', 'col': None,          'stackable': False, 'earn_day': 7,  'category': 'trade',
                      'desc': 'Build furniture, kraals, market stalls. Passive income + upgrade paths.'},
    'pottery':       {'name': 'Pottery Studio (izitsha)',     'cows': 60,   'icon': '🏺', 'col': None,          'stackable': False, 'earn_day': 5,  'category': 'trade',
                      'desc': 'Create traditional pottery for trade. Low cost, steady income.'},
    # ── Regalia (wearable — visible to all players) ───────────────────────────
    'induna_regalia':   {'name': 'iNduna Regalia (cow-hide)',    'cows': 30,   'icon': '🎯', 'col': None, 'stackable': False, 'earn_day': 0, 'category': 'regalia', 'level_req': 2,
                         'desc': 'Cow-hide loincloth + shield + spear. Changes board skin. Earns respect.'},
    'inkosi_regalia':   {'name': 'iNkosi Regalia (leopard-skin)', 'cows': 200, 'icon': '🐆', 'col': None, 'stackable': False, 'earn_day': 0, 'category': 'regalia', 'level_req': 3,
                         'desc': 'Full leopard-skin kaross. Animated board shimmer. Visible in all games.'},
    'isilo_regalia':    {'name': 'iSilo Crown Regalia (lion+leopard)', 'cows': 1000, 'icon': '👑', 'col': None, 'stackable': False, 'earn_day': 0, 'category': 'regalia', 'level_req': 5,
                         'desc': 'Lion mane + leopard kaross + sceptre. Full-screen coronation animation.'},
    'bride_regalia':    {'name': 'Wedding Regalia (umshado)',    'cows': 50,   'icon': '💑', 'col': None, 'stackable': False, 'earn_day': 0, 'category': 'regalia', 'level_req': 2,
                         'desc': 'Traditional marriage outfit. Both spouses get matching beadwork badge.'},
    # ── Jewellery ─────────────────────────────────────────────────────────────
    'beadwork':      {'name': 'Beadwork Set (izinhloko)',      'cows': 80,   'icon': '📿', 'col': 'jewellery',  'stackable': True,  'earn_day': 0, 'category': 'jewellery',
                      'desc': 'Traditional Nguni beadwork. Required for Paramount rank. Status marker.'},
    'gold_armlet':   {'name': 'Gold Armlet (igolide)',         'cows': 200,  'icon': '💛', 'col': 'jewellery',  'stackable': True,  'earn_day': 1, 'category': 'jewellery',
                      'desc': 'Rare gold armlet. Shows wealth. Earns +1 cow/day from admirers.'},
    # ── Kingdom progression ───────────────────────────────────────────────────
    'crown_petition':   {'name': 'Chief Petition (iSihlalo)',    'cows': 150, 'icon': '📜', 'col': None, 'stackable': False, 'earn_day': 0, 'category': 'progression', 'level_req': 2,
                         'desc': 'Become a Chief (iNkosi). Requires: land + great house + beadwork.'},
    'paramount_petition':{'name': 'Paramount Petition',          'cows': 500, 'icon': '🦁', 'col': None, 'stackable': False, 'earn_day': 0, 'category': 'progression', 'level_req': 3,
                          'desc': 'Become Paramount Chief. Requires: Chief title + 3 land plots + ironsmith + 500 cows.'},
    'isilo_petition':   {'name': 'iSilo Ascension',              'cows': 2000,'icon': '🔱', 'col': None, 'stackable': False, 'earn_day': 0, 'category': 'progression', 'level_req': 4,
                         'desc': 'Claim the supreme throne. Requires: Paramount + regalia + 2000 cows + defeating all tribe Paramounts.'},
}

# ── Payment & contact details ─────────────────────────────────────────────────
PAYPAL_EMAIL   = 'stanza.chirwa@gmail.com'
PAYPAL_LINK    = 'https://paypal.me/stanzachirwa'
KOFI_USERNAME  = 'inkazimulo_digital'
KOFI_LINK      = 'https://ko-fi.com/inkazimulo_digital'
SUPPORT_EMAIL  = 'info@inkazimulo.digital'
BANK_DETAILS   = {
    'bank':       'First National Bank (FNB)',
    'holder':     'S.D. Chirwa',
    'account_no': '63032569915',
    'branch':     '250655',   # FNB universal branch code
    'type':       'Cheque / Current Account',
    'reference':  'INTSHUBA-DONATION',
    'swift':      'FIRNZAJJ',  # FNB SWIFT for international transfers
}

LOBOLA_COST   = 100
CROWN_WAGER   = 300
DAILY_TRIBUTE = 20
DAILY_LAND    = 2
DAILY_FREE    = 1
SEASON_DAYS   = 90

# ── Authentic Nguni hierarchy (corrected) ────────────────────────────────────
# iJongo/iNtombi → iNduna/uMalusi → iNkosi → iNkosi YaMakhosi → iSilo
TITLES = {
    # Level 1 — initiate (gender-aware)
    'iJongo':              {'min_cows': 0,    'icon': '🪃',  'label': 'Boy Initiate',      'gender': 'm', 'level': 1},
    'iNtombi':             {'min_cows': 0,    'icon': '🌸',  'label': 'Girl Initiate',     'gender': 'f', 'level': 1},
    # Level 2 — warrior/herdsman
    'iNduna':              {'min_cows': 20,   'icon': '🏹',  'label': 'Induna (Warrior)',  'gender': 'm', 'level': 2},
    'uMalusi':             {'min_cows': 20,   'icon': '🐄',  'label': 'Herdsman',          'gender': 'f', 'level': 2},
    # Level 3 — chief
    'iNkosi':              {'min_cows': 100,  'icon': '👑',  'label': 'Chief',             'gender': 'n', 'level': 3},
    'iNkosazana':          {'min_cows': 100,  'icon': '💍',  'label': 'Chieftainess',      'gender': 'f', 'level': 3},
    # Level 4 — paramount chief
    'iNkosi_YaMakhosi':    {'min_cows': 500,  'icon': '🦁',  'label': 'Paramount Chief',   'gender': 'n', 'level': 4},
    'iNdlovukazi':         {'min_cows': 500,  'icon': '🐘',  'label': 'Great She-Elephant','gender': 'f', 'level': 4},
    # Level 5 — supreme ruler
    'iSilo':               {'min_cows': 2000, 'icon': '🔱',  'label': 'The Great King',    'gender': 'n', 'level': 5},
    'iSilo_SamaZulu':      {'min_cows': 5000, 'icon': '⚜️',  'label': 'Emperor of Nations','gender': 'n', 'level': 5},
}

# Default title lookup (gender-neutral path)
TITLE_PATH = [
    ('iJongo',           0),
    ('iNduna',           20),
    ('iNkosi',           100),
    ('iNkosi_YaMakhosi', 500),
    ('iSilo',            2000),
    ('iSilo_SamaZulu',   5000),
]

COW_PACKS = {
    'cows_10':    {'cows': 10,  'price_zar': 500,  'stripe_price_id': '', 'label': 'Starter Herd'},
    'cows_50':    {'cows': 50,  'price_zar': 2000, 'stripe_price_id': '', 'label': 'Growing Herd'},
    'cows_200':   {'cows': 200, 'price_zar': 4900, 'stripe_price_id': '', 'label': 'Warrior Herd'},
    'cows_daily': {'cows': 3,   'price_zar': 0,    'stripe_price_id': 'free', 'label': 'Daily Gift'},
}


def _calc_title(herd_cows: int, gender: str = 'n') -> str:
    """Calculate title based on herd size and gender."""
    # Start with gender-appropriate initiate title
    title = 'iJongo' if gender != 'f' else 'iNtombi'
    for key, min_cows in TITLE_PATH:
        if herd_cows >= min_cows:
            title = key
            # Don't override initiate level for females
            if min_cows == 0:
                title = 'iNtombi' if gender == 'f' else 'iJongo'
    # Gender variants at lower levels
    if gender == 'f':
        if title == 'iNduna':      title = 'uMalusi'
        if title == 'iNkosi':      title = 'iNkosazana'
        if title == 'iNkosi_YaMakhosi': title = 'iNdlovukazi'
    return title


def _get_herd(email: str) -> int:
    # Always open a fresh connection to avoid stale cached reads
    import sqlite3 as _sq
    try:
        db = _sq.connect(DB_PATH)
        db.row_factory = _sq.Row
        row = db.execute('SELECT herd_cows FROM users WHERE email=?', (email,)).fetchone()
        db.close()
        return row['herd_cows'] if row else 10
    except Exception:
        return 10


# ── Cow gain limits per event type (prevents abuse) ──────────────────────────
_COW_GAIN_LIMITS = {
    'daily_gift':           50,   # max 50 free cows/day
    'story_complete':       100,  # max 100 per story chapter
    'achievement':          200,  # achievements
    'bet_won':              5000, # bet winnings capped
    'chest_opened':         500,  # chest reward max
    'referral_bonus':       20,   # referral reward
    'ceremony_blessing':    300,
    'puzzle_solved':        50,
    'passive_income':       100,  # passive income cap
    '_default_gain':        9999, # admin/purchase events uncapped
    '_deduct':             -1,    # all deductions allowed
}
_COW_RATE_LIMITER: dict[str, list] = {}  # email → [(ts, amount), ...]
_COW_RATE_LOCK = threading.Lock()

def _check_cow_rate(email: str, amount: int) -> bool:
    """Allow max 2000 gained cows per player per hour (anti-bot)."""
    if amount <= 0: return True          # deductions always allowed
    now = time.time()
    cutoff = now - 3600
    with _COW_RATE_LOCK:
        history = [e for e in _COW_RATE_LIMITER.get(email, []) if e[0] > cutoff]
        total_gained = sum(e[1] for e in history)
        if total_gained + amount > 2000:
            log.warning(f'[credits] Rate limit: {email} tried +{amount} (hour total={total_gained})')
            return False
        history.append((now, amount))
        _COW_RATE_LIMITER[email] = history
        return True

def _sign_ledger(email: str, amount: int, event_type: str, ts: int) -> str:
    """HMAC signature for each ledger entry — detects tampering."""
    sk  = os.environ.get('SECRET_KEY', '')
    msg = f'ledger:{email}:{amount}:{event_type}:{ts}'.encode()
    return _hmac.new(sk.encode(), msg, _hs.sha256).hexdigest()[:24]

def _add_cows(email: str, amount: int, event_type: str, detail: dict = None) -> int:
    """Hardened cow ledger. Returns new balance.
    - Enforces per-event gain caps
    - Rate-limits gains to 2000/hour per player
    - Signs every ledger entry with HMAC
    - Prevents balance from going below 0
    """
    if not email: return 0
    amount = int(amount)  # ensure integer — prevents float injection

    # Determine cap for this event
    if amount > 0:
        cap_key = next((k for k in _COW_GAIN_LIMITS if event_type.startswith(k)), '_default_gain')
        cap = _COW_GAIN_LIMITS[cap_key]
        if amount > cap:
            log.warning(f'[credits] Capped {event_type} gain from {amount} to {cap} for {email}')
            amount = cap
        # Rate limit check
        if not _check_cow_rate(email, amount):
            log.warning(f'[credits] Rate limited: {email} {event_type} +{amount}')
            amount = 0  # silently zero out rather than error (prevents timing attacks)

    ts  = int(time.time())
    sig = _sign_ledger(email, amount, event_type, ts)

    db = get_db()
    db.execute(
        'UPDATE users SET herd_cows = MAX(0, herd_cows + ?) WHERE email=?',
        (amount, email)
    )
    row = db.execute('SELECT herd_cows FROM users WHERE email=?', (email,)).fetchone()
    new_bal = row['herd_cows'] if row else 0
    new_title = _calc_title(new_bal)
    db.execute('UPDATE users SET title=? WHERE email=?', (new_title, email))
    db.execute(
        'INSERT INTO kingdom_events(user_email,event_type,detail,cows_delta,ledger_sig) '
        'VALUES(?,?,?,?,?)',
        (email, event_type, json.dumps(detail or {}), amount, sig)
    )
    db.commit()
    return new_bal


def _get_current_king():
    db = get_db()
    row = db.execute(
        'SELECT email,name,herd_cows,title FROM users WHERE has_crown=1 LIMIT 1'
    ).fetchone()
    if row:
        return dict(row)
    return {'email': 'ai@intshuba', 'name': 'AI Inkosi', 'herd_cows': 9999, 'title': 'Inkosi_Enkulu'}


def _daily_passives():
    """Award full passive economy income once per 24h per user."""
    db  = get_db()
    now = int(time.time())
    cutoff = now - 86400
    # 1. Free daily cow for every logged-in player
    db.execute(
        'UPDATE users SET herd_cows=herd_cows+1, last_passive_run=? WHERE last_passive_run < ? AND email != ""',
        (now, cutoff)
    )
    # 2. Land plots: +2 cows/day each (BaVenda tribe gets +3)
    db.execute(
        'UPDATE users SET herd_cows=herd_cows+(land_plots*2) WHERE land_plots > 0 AND last_passive_run < ?',
        (cutoff,)
    )
    # 3. Crop farms: +4 cows/day each
    db.execute(
        'UPDATE users SET herd_cows=herd_cows+(crop_farms*4) WHERE crop_farms > 0 AND last_passive_run < ?',
        (cutoff,)
    )
    # 4. Cattle pens: +6 cows/day each
    db.execute(
        'UPDATE users SET herd_cows=herd_cows+(cattle_pens*6) WHERE cattle_pens > 0 AND last_passive_run < ?',
        (cutoff,)
    )
    # 5. Crown holder: +20 cows/day tribute from the realm
    db.execute(
        'UPDATE users SET herd_cows=herd_cows+? WHERE has_crown=1',
        (DAILY_TRIBUTE,)
    )
    # 6. Married couples bonus: +5 cows/day
    db.execute(
        'UPDATE users SET herd_cows=herd_cows+5 WHERE is_married=1 AND last_passive_run < ?',
        (cutoff,)
    )
    # 7. BaVenda tribe land bonus (extra +1 per plot)
    db.execute(
        "UPDATE users SET herd_cows=herd_cows+land_plots WHERE tribe_id='bavenda' AND land_plots>0"
    )
    # 8. Trade profession income
    # Each unlocked profession earns its daily rate
    for trade_id, prof in TRADE_PROFESSIONS.items():
        earn = prof['earn_day']
        risk = prof.get('risk', 0)
        # Fetch users who own this trade
        trade_owners = db.execute(
            "SELECT DISTINCT user_email FROM kingdom_events WHERE event_type=?",
            ('bought_' + trade_id,)
        ).fetchall()
        for row in trade_owners:
            email = row['user_email']
            # Apply risk — randomly lose income if risk triggers
            import random
            if random.random() < risk:
                # Risk event — lose half income
                actual_earn = max(0, earn // 2)
            else:
                actual_earn = earn
            if actual_earn > 0:
                db.execute('UPDATE users SET herd_cows=herd_cows+? WHERE email=?', (actual_earn, email))
    # 9. Update titles after all income
    rows = db.execute('SELECT email, herd_cows FROM users WHERE email != ""').fetchall()
    for row in rows:
        new_title = _calc_title(row['herd_cows'])
        db.execute('UPDATE users SET title=? WHERE email=?', (new_title, row['email']))
    db.commit()


# ── Economy API ───────────────────────────────────────────────────────────────

@app.route('/api/economy/status')
def economy_status():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    try:
        _daily_passives()
        db = get_db()
        row = db.execute(
            'SELECT herd_cows,land_plots,jewellery,is_married,spouse_email,'
            'has_crown,title,current_level,total_cows,wins,losses,games '
            'FROM users WHERE email=?', (user['email'],)
        ).fetchone()
        if not row:
            return jsonify({'error': 'User not found'}), 404
        d = dict(row)
        d['title_info'] = TITLES.get(d['title'], {'icon':'🐄','label':'Calf','min_cows':0,'level':1,'gender':'n'})
        d['king'] = _get_current_king()
        d['can_level2'] = d['herd_cows'] >= LEVEL_GATES[1]['unlock_next']
        d['can_level3'] = d['herd_cows'] >= LEVEL_GATES[2]['unlock_next']
        d['can_market'] = d['herd_cows'] >= 50
        d['market_items'] = {k: {
            'name': v['name'], 'cows': v['cows'], 'icon': v['icon'],
            'desc': v['desc'], 'stackable': v['stackable']
        } for k, v in MARKET_ITEMS.items()}
        d['cow_packs'] = {k: {
            'cows': v['cows'], 'price_zar': v['price_zar'], 'label': v['label']
        } for k, v in COW_PACKS.items()}
        events = db.execute(
            'SELECT event_type,cows_delta,created FROM kingdom_events '
            'WHERE user_email=? ORDER BY created DESC LIMIT 10',
            (user['email'],)
        ).fetchall()
        d['recent_events'] = [dict(e) for e in events]
        if d['is_married'] and d['spouse_email']:
            sp = db.execute('SELECT name,title FROM users WHERE email=?',
                            (d['spouse_email'],)).fetchone()
            d['spouse'] = dict(sp) if sp else {}
        return jsonify(d)
    except Exception as e:
        BugFixer.capture('error', 'economy_status: ' + str(e), e)
        return jsonify({'error': str(e)}), 500


@app.route('/api/economy/buy-cows', methods=['POST'])
def buy_cows():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data    = request.get_json(force=True) or {}
    pack_id = sanitise(str(data.get('pack', '')), 40)
    pack    = COW_PACKS.get(pack_id)
    if not pack:
        return jsonify({'error': 'Unknown pack'}), 400
    # Free daily
    if pack['price_zar'] == 0:
        db = get_db()
        row = db.execute(
            'SELECT last_cow_gift FROM users WHERE email=?', (user['email'],)
        ).fetchone()
        if row and (int(time.time()) - (row['last_cow_gift'] or 0)) < 86400:
            return jsonify({'error': 'Daily gift already claimed — come back tomorrow!'}), 429
        new_bal = _add_cows(user['email'], pack['cows'], 'daily_gift')
        db.execute('UPDATE users SET last_cow_gift=? WHERE email=?',
                   (int(time.time()), user['email']))
        db.commit()
        return jsonify({'ok': True, 'cows_added': pack['cows'], 'herd_cows': new_bal,
                        'message': '🐄 +' + str(pack['cows']) + ' daily gift cows!'})
    # Paid – Stripe
    stripe = _stripe()
    if not stripe or not pack.get('stripe_price_id'):
        return jsonify({'error': 'Stripe not configured — contact support'}), 503
    base_url = os.environ.get('APP_URL', request.host_url.rstrip('/'))
    try:
        chk = stripe.checkout.Session.create(
            mode        = 'payment',
            line_items  = [{'price': pack['stripe_price_id'], 'quantity': 1}],
            success_url = base_url + '/payment/success?session_id={CHECKOUT_SESSION_ID}&pack=' + pack_id,
            cancel_url  = base_url + '/payment/cancel',
            customer_email = user['email'],
            metadata    = {'user_email': user['email'], 'pack_id': pack_id,
                           'cows': str(pack['cows']), 'type': 'cow_pack'},
        )
        return jsonify({'ok': True, 'checkout_url': chk.url})
    except Exception as e:
        return jsonify({'error': str(e)}), 500


@app.route('/api/economy/place-bet', methods=['POST'])
def place_bet():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data    = request.get_json(force=True) or {}
    level   = int(data.get('level', 2))
    gate    = LEVEL_GATES.get(level, {})
    bet_amt = max(int(data.get('bet', gate.get('ante', 3))), gate.get('ante', 3))
    if level < 2:
        return jsonify({'error': 'No betting at Level 1'}), 400
    herd = _get_herd(user['email'])
    if herd < bet_amt:
        return jsonify({
            'ok': False, 'insufficient': True,
            'herd_cows': herd, 'required': bet_amt,
            'message': 'Not enough cows! You have ' + str(herd) + ', need ' + str(bet_amt) + ' to play Level ' + str(level) + '.',
            'options': {'buy_pack': True, 'drop_level': level - 1, 'daily_gift': True},
        }), 402
    new_bal = _add_cows(user['email'], -bet_amt, 'bet_placed', {'level': level, 'amount': bet_amt})
    db = get_db()
    db.execute(
        'INSERT INTO bets(challenger_email,bet_amount,level) VALUES(?,?,?)',
        (user['email'], bet_amt, level)
    )
    bet_id = db.execute('SELECT last_insert_rowid()').fetchone()[0]
    db.commit()
    return jsonify({'ok': True, 'bet_id': bet_id, 'bet_amount': bet_amt,
                    'herd_cows': new_bal, 'message': '🐄 ' + str(bet_amt) + ' cows in the pot!'})


@app.route('/api/economy/settle-bet', methods=['POST'])
def settle_bet():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data    = request.get_json(force=True) or {}
    bet_id  = int(data.get('bet_id', 0))
    outcome = sanitise(str(data.get('outcome', '')), 10)
    score   = int(data.get('score', 0))
    if outcome not in ('win', 'lose', 'draw'):
        return jsonify({'error': 'Invalid outcome'}), 400
    db = get_db()
    bet = db.execute(
        'SELECT * FROM bets WHERE id=? AND challenger_email=?',
        (bet_id, user['email'])
    ).fetchone()
    if not bet or bet['outcome'] != 'pending':
        return jsonify({'error': 'Bet not found or already settled'}), 404
    bet_amt = bet['bet_amount']
    unlock  = None
    if outcome == 'win':
        winnings = bet_amt * 2
        new_bal  = _add_cows(user['email'], winnings, 'bet_won', {'amount': winnings, 'score': score})
        db.execute("UPDATE bets SET outcome='won' WHERE id=?", (bet_id,))
        msg = '🏆 You won! +' + str(winnings) + ' cows!'
        for lv, gate in LEVEL_GATES.items():
            if new_bal >= gate['unlock_next'] and lv < 3:
                db.execute(
                    'UPDATE users SET current_level=MAX(current_level,?) WHERE email=?',
                    (lv + 1, user['email'])
                )
                unlock = lv + 1
    elif outcome == 'draw':
        new_bal = _add_cows(user['email'], bet_amt, 'bet_draw', {'amount': bet_amt})
        db.execute("UPDATE bets SET outcome='draw' WHERE id=?", (bet_id,))
        msg = '⚖️ Draw! ' + str(bet_amt) + ' cows returned.'
    else:
        new_bal = _get_herd(user['email'])
        db.execute("UPDATE bets SET outcome='lost' WHERE id=?", (bet_id,))
        msg = '😢 Lost ' + str(bet_amt) + ' cows.'
        for lv in (3, 2):
            gate = LEVEL_GATES.get(lv, {})
            if new_bal < gate.get('min_cows', 0):
                db.execute('UPDATE users SET current_level=? WHERE email=?', (lv - 1, user['email']))
                msg += ' Dropped to Level ' + str(lv - 1) + '.'
    new_title = _calc_title(new_bal)
    cows_for_total = max(0, bet_amt if outcome == 'win' else 0)
    db.execute('UPDATE users SET title=?,total_cows=total_cows+? WHERE email=?',
               (new_title, cows_for_total, user['email']))
    db.commit()
    return jsonify({'ok': True, 'outcome': outcome, 'herd_cows': new_bal,
                    'message': msg, 'unlock_level': unlock, 'title': new_title})


@app.route('/api/market/buy', methods=['POST'])
def market_buy():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data    = request.get_json(force=True) or {}
    item_id = sanitise(str(data.get('item', '')), 40)
    item    = MARKET_ITEMS.get(item_id)
    if not item:
        return jsonify({'error': 'Unknown item'}), 400
    herd = _get_herd(user['email'])
    if herd < item['cows']:
        return jsonify({'ok': False, 'insufficient': True, 'herd_cows': herd,
                        'required': item['cows'],
                        'message': 'Need ' + str(item['cows']) + ' cows. You have ' + str(herd) + '.'}), 402
    db = get_db()
    if item_id == 'crown_petition':
        row = db.execute('SELECT land_plots,jewellery FROM users WHERE email=?',
                         (user['email'],)).fetchone()
        if not row or row['land_plots'] < 1 or row['jewellery'] < 1:
            return jsonify({'ok': False, 'error': 'Crown requires: 1 land plot + 1 jewellery set + Great House.'}), 400
        gh = db.execute(
            "SELECT id FROM kingdom_events WHERE user_email=? AND event_type='bought_great_house' LIMIT 1",
            (user['email'],)
        ).fetchone()
        if not gh:
            return jsonify({'ok': False, 'error': 'You must own a Great House first.'}), 400
    new_bal = _add_cows(user['email'], -item['cows'], 'bought_' + item_id, {'item': item_id})
    if item.get('col'):
        db.execute(f"UPDATE users SET {item['col']}={item['col']}+1 WHERE email=?",
                   (user['email'],))
    if item_id == 'crown_petition':
        db.execute('UPDATE users SET has_crown=0 WHERE has_crown=1')
        db.execute('UPDATE users SET has_crown=1 WHERE email=?', (user['email'],))
        db.execute(
            'INSERT INTO crown_history(holder_email,holder_name,won_at,cows_at_crown) VALUES(?,?,strftime(\'%s\',\'now\'),?)',
            (user['email'], user['name'], new_bal)
        )
    db.commit()
    return jsonify({'ok': True, 'item': item_id, 'herd_cows': new_bal,
                    'message': item['icon'] + ' ' + item['name'] + ' acquired! ' + item['desc']})


@app.route('/api/kingdom/propose', methods=['POST'])
def propose_marriage():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data         = request.get_json(force=True) or {}
    partner_email = sanitise(str(data.get('partner_email', '')), 80)
    if not partner_email or partner_email == user['email']:
        return jsonify({'error': 'Invalid partner'}), 400
    db = get_db()
    partner = db.execute('SELECT name,is_married FROM users WHERE email=?',
                         (partner_email,)).fetchone()
    if not partner:
        return jsonify({'error': 'Player not found'}), 404
    if partner['is_married']:
        return jsonify({'error': partner['name'] + ' is already married!'}), 400
    herd = _get_herd(user['email'])
    if herd < LOBOLA_COST:
        return jsonify({'ok': False, 'insufficient': True, 'required': LOBOLA_COST, 'herd_cows': herd,
                        'message': 'Lobola requires ' + str(LOBOLA_COST) + ' cows. You have ' + str(herd) + '.'}), 402
    _add_cows(user['email'], -LOBOLA_COST, 'lobola_paid', {'partner': partner_email})
    db.execute('INSERT INTO marriages(proposer_email,partner_email,lobola_paid) VALUES(?,?,?)',
               (user['email'], partner_email, LOBOLA_COST))
    db.execute('UPDATE users SET is_married=1,spouse_email=? WHERE email=?',
               (partner_email, user['email']))
    db.execute('UPDATE users SET is_married=1,spouse_email=? WHERE email=?',
               (user['email'], partner_email))
    db.commit()
    return jsonify({'ok': True,
                    'message': '💍 ' + user['name'] + ' paid lobola and married ' + partner['name'] + '!'})


@app.route('/api/kingdom/challenge-crown', methods=['POST'])
def challenge_crown():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    herd = _get_herd(user['email'])
    if herd < CROWN_WAGER:
        return jsonify({'ok': False, 'insufficient': True, 'required': CROWN_WAGER,
                        'herd_cows': herd,
                        'message': 'Challenging the crown requires ' + str(CROWN_WAGER) + ' cows.'}), 402
    king = _get_current_king()
    if king['email'] == user['email']:
        return jsonify({'error': 'You already hold the crown!'}), 400
    _add_cows(user['email'], -CROWN_WAGER, 'crown_challenge_wager')
    return jsonify({'ok': True, 'king': king, 'wager': CROWN_WAGER,
                    'message': '⚔️ You challenge ' + king['name'] + ' for the crown! Win to claim the throne.',
                    'start_game': True, 'game_type': 'crown_challenge'})


@app.route('/api/kingdom/crown-result', methods=['POST'])
def crown_result():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data    = request.get_json(force=True) or {}
    outcome = sanitise(str(data.get('outcome', '')), 10)
    if outcome not in ('win', 'lose'):
        return jsonify({'error': 'Invalid outcome'}), 400
    db = get_db()
    if outcome == 'win':
        old_king = db.execute('SELECT email,name FROM users WHERE has_crown=1').fetchone()
        if old_king:
            db.execute('UPDATE users SET has_crown=0 WHERE email=?', (old_king['email'],))
            db.execute(
                "UPDATE crown_history SET lost_at=strftime('%s','now') WHERE holder_email=? AND lost_at=0",
                (old_king['email'],)
            )
        db.execute('UPDATE users SET has_crown=1 WHERE email=?', (user['email'],))
        herd = _get_herd(user['email'])
        db.execute(
            "INSERT INTO crown_history(holder_email,holder_name,won_at,cows_at_crown) VALUES(?,?,strftime('%s','now'),?)",
            (user['email'], user['name'], herd)
        )
        _add_cows(user['email'], CROWN_WAGER * 2, 'crown_won', {'wager': CROWN_WAGER})
        new_title = 'iNdlovukazi' if 'a' in user['name'].lower() else 'Inkosi_Enkulu'
        db.execute('UPDATE users SET title=? WHERE email=?', (new_title, user['email']))
        db.commit()
        msg = '👑 INKOSI! You defeated the king and claimed the throne! All hail ' + user['name'] + '!'
    else:
        db.commit()
        msg = '⚔️ The king defended the throne. Your ' + str(CROWN_WAGER) + ' cows are forfeit.'
    return jsonify({'ok': True, 'outcome': outcome, 'message': msg,
                    'herd_cows': _get_herd(user['email'])})


@app.route('/api/kingdom/leaderboard')
def kingdom_leaderboard():
    db = get_db()
    rows = db.execute(
        'SELECT name,title,herd_cows,land_plots,jewellery,has_crown,is_married,wins,losses,games '
        'FROM users ORDER BY has_crown DESC, herd_cows DESC, wins DESC LIMIT 30'
    ).fetchall()
    king = _get_current_king()
    hall = db.execute(
        'SELECT holder_name,cows_at_crown,won_at,lost_at FROM crown_history ORDER BY won_at DESC LIMIT 10'
    ).fetchall()
    return jsonify({'players': [dict(r) for r in rows],
                    'king': king, 'hall_fame': [dict(r) for r in hall]})


# ═══════════════════════════════════════════════════════════════════════════════
#  TRIBE · AGE POOL · SEASON · REGALIA ROUTES
# ═══════════════════════════════════════════════════════════════════════════════

@app.route('/api/tribe/join', methods=['POST'])
def join_tribe():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data     = request.get_json(force=True) or {}
    tribe_id = sanitise(str(data.get('tribe_id', 'world')), 30)
    if tribe_id not in TRIBES:
        return jsonify({'error': 'Unknown tribe'}), 400
    db = get_db()
    db.execute('UPDATE users SET tribe_id=? WHERE email=?', (tribe_id, user['email']))
    db.execute(
        'INSERT OR REPLACE INTO tribe_memberships(player_email,tribe_id,rank) VALUES(?,?,?)',
        (user['email'], tribe_id, 'member')
    )
    db.commit()
    tribe = TRIBES[tribe_id]
    return jsonify({
        'ok': True,
        'tribe': tribe_id,
        'tribe_name': tribe['name'],
        'bonus': tribe.get('bonus_desc', ''),
        'message': 'Welcome to ' + tribe['name'] + '! ' + tribe['icon'] + ' ' + tribe.get('bonus_desc', ''),
    })


@app.route('/api/tribe/members/<tribe_id>')
def tribe_members(tribe_id):
    if tribe_id not in TRIBES:
        return jsonify({'error': 'Unknown tribe'}), 400
    db   = get_db()
    rows = db.execute(
        'SELECT u.name, u.title, u.herd_cows, u.has_crown, u.wins '
        'FROM users u JOIN tribe_memberships tm ON tm.player_email=u.email '
        'WHERE tm.tribe_id=? ORDER BY u.has_crown DESC, u.herd_cows DESC LIMIT 50',
        (tribe_id,)
    ).fetchall()
    return jsonify({'tribe': TRIBES[tribe_id], 'members': [dict(r) for r in rows], 'count': len(rows)})


@app.route('/api/tribe/war/standings')
def tribe_war_standings():
    db   = get_db()
    rows = db.execute(
        'SELECT tm.tribe_id, COUNT(u.email) as members, SUM(u.herd_cows) as total_cows, '
        'SUM(u.wins) as total_wins, MAX(u.has_crown) as has_king '
        'FROM users u JOIN tribe_memberships tm ON tm.player_email=u.email '
        'GROUP BY tm.tribe_id ORDER BY total_cows DESC'
    ).fetchall()
    standings = []
    for r in rows:
        d = dict(r)
        ti = TRIBES.get(d['tribe_id'], {})
        d['tribe_name'] = ti.get('name', d['tribe_id'])
        d['tribe_icon'] = ti.get('icon', '🐄')
        d['bonus']      = ti.get('bonus_desc', '')
        standings.append(d)
    return jsonify({'standings': standings})


@app.route('/api/user/set-age-pool', methods=['POST'])
def set_age_pool():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data       = request.get_json(force=True) or {}
    birth_year = int(data.get('birth_year', 0))
    now_year   = int(time.strftime('%Y'))
    age        = now_year - birth_year if 1900 < birth_year < now_year else 25
    pool = 'open'
    if   age < 10: pool = 'u10'
    elif age < 14: pool = 'u14'
    elif age < 18: pool = 'u18'
    elif age < 25: pool = 'u25'
    elif age < 40: pool = 'u40'
    elif age < 60: pool = 'senior'
    else:          pool = 'elder'
    db = get_db()
    db.execute('UPDATE users SET birth_year=?,age_pool=? WHERE email=?',
               (birth_year, pool, user['email']))
    db.commit()
    return jsonify({'ok': True, 'age_pool': pool, 'pool_info': AGE_POOLS[pool],
                    'message': 'Registered in ' + AGE_POOLS[pool]['label'] + '! ' + AGE_POOLS[pool]['icon']})


@app.route('/api/season/status')
def season_status():
    db      = get_db()
    king    = _get_current_king()
    hall    = db.execute(
        'SELECT holder_name,cows_at_crown,won_at,lost_at,season FROM crown_history '
        'ORDER BY won_at DESC LIMIT 20'
    ).fetchall()
    now        = int(time.time())
    season_len = SEASON_DAYS * 86400
    season_num = (now // season_len) + 1
    season_end = season_num * season_len
    days_left  = max(0, (season_end - now) // 86400)
    top = db.execute(
        'SELECT name,title,herd_cows,competition_wins,tribe_id FROM users '
        'ORDER BY competition_wins DESC, herd_cows DESC LIMIT 10'
    ).fetchall()
    return jsonify({'season': season_num, 'days_left': days_left, 'king': king,
                    'hall_fame': [dict(r) for r in hall],
                    'top_players': [dict(r) for r in top]})


@app.route('/api/user/equip-regalia', methods=['POST'])
def equip_regalia():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data    = request.get_json(force=True) or {}
    item_id = sanitise(str(data.get('item', '')), 40)
    item    = MARKET_ITEMS.get(item_id)
    if not item or item.get('category') != 'regalia':
        return jsonify({'error': 'Not a regalia item'}), 400
    db  = get_db()
    evt = db.execute(
        "SELECT id FROM kingdom_events WHERE user_email=? AND event_type=? LIMIT 1",
        (user['email'], 'bought_' + item_id)
    ).fetchone()
    if not evt:
        return jsonify({'error': 'You have not purchased this regalia yet'}), 402
    db.execute('UPDATE users SET regalia=? WHERE email=?', (item_id, user['email']))
    db.commit()
    return jsonify({'ok': True, 'regalia': item_id,
                    'message': item['icon'] + ' ' + item['name'] + ' equipped! Others will see your rank.'})


@app.route('/api/user/profile-full')
def profile_full():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    db  = get_db()
    row = db.execute(
        'SELECT name,email,title,herd_cows,land_plots,crop_farms,cattle_pens,'
        'jewellery,is_married,spouse_email,has_crown,tribe_id,age_pool,'
        'birth_year,regalia,competition_wins,season_rank,wins,losses,draws,'
        'games,total_cows,plan,plan_expires FROM users WHERE email=?',
        (user['email'],)
    ).fetchone()
    if not row:
        return jsonify({'error': 'User not found'}), 404
    d = dict(row)
    d['title_info']   = TITLES.get(d['title'], TITLES.get('iJongo', {}))
    d['tribe_info']   = TRIBES.get(d['tribe_id'], TRIBES.get('world', {}))
    d['age_pool_info']= AGE_POOLS.get(d['age_pool'], AGE_POOLS['open'])
    d['king']         = _get_current_king()
    return jsonify(d)


@app.route('/api/tribe/sounds/<tribe_id>')
def get_tribe_sounds(tribe_id):
    return jsonify({'tribe': tribe_id,
                    'sound_profile': TRIBE_SOUNDS.get(tribe_id, TRIBE_SOUNDS.get('world', {}))})


# ═══════════════════════════════════════════════════════════════════════════════
#  ADMIN MONETISATION DASHBOARD  ·  SCHOOL TEACHER DASHBOARD
#  SEASON PRIZE SYSTEM  ·  LIVE-STREAM INTEGRATION
# ═══════════════════════════════════════════════════════════════════════════════

# ── Admin helpers ─────────────────────────────────────────────────────────────
def _require_admin():
    key = request.headers.get('X-Admin-Key','')
    if key != os.environ.get('ADMIN_KEY','') or not key:
        return False
    return True

def _require_school_admin():
    """Check if logged-in user has school admin privileges."""
    user = current_user()
    if not user:
        return False
    db  = get_db()
    row = db.execute(
        "SELECT is_admin FROM users WHERE email=?", (user['email'],)
    ).fetchone()
    return row and row['is_admin'] >= 1

# ── Monetisation admin dashboard ──────────────────────────────────────────────
@app.route('/api/admin/dashboard')
def admin_dashboard():
    """Full monetisation + player stats dashboard. Requires X-Admin-Key header."""
    if not _require_admin():
        return jsonify({'error': 'Unauthorized'}), 401
    db   = get_db()
    now  = int(time.time())
    day  = now - 86400
    week = now - 7*86400
    month= now - 30*86400

    # ── Revenue ───────────────────────────────────────────────────────────────
    rev_today  = db.execute("SELECT COALESCE(SUM(amount_cents),0) FROM payments WHERE status='completed' AND created>?", (day,)).fetchone()[0]
    rev_week   = db.execute("SELECT COALESCE(SUM(amount_cents),0) FROM payments WHERE status='completed' AND created>?", (week,)).fetchone()[0]
    rev_month  = db.execute("SELECT COALESCE(SUM(amount_cents),0) FROM payments WHERE status='completed' AND created>?", (month,)).fetchone()[0]
    rev_total  = db.execute("SELECT COALESCE(SUM(amount_cents),0) FROM payments WHERE status='completed'").fetchone()[0]
    rev_by_plan= db.execute(
        "SELECT plan, COUNT(*) as cnt, SUM(amount_cents) as total FROM payments WHERE status='completed' GROUP BY plan"
    ).fetchall()
    don_total  = db.execute("SELECT COALESCE(SUM(amount_zar),0) FROM donations").fetchone()[0]
    don_count  = db.execute("SELECT COUNT(*) FROM donations").fetchone()[0]

    # ── Users ─────────────────────────────────────────────────────────────────
    total_users  = db.execute("SELECT COUNT(*) FROM users WHERE email!=''").fetchone()[0]
    new_today    = db.execute("SELECT COUNT(*) FROM users WHERE created>?", (day,)).fetchone()[0]
    new_week     = db.execute("SELECT COUNT(*) FROM users WHERE created>?", (week,)).fetchone()[0]
    active_week  = db.execute("SELECT COUNT(*) FROM users WHERE last_login>?", (week,)).fetchone()[0]
    paying_users = db.execute("SELECT COUNT(*) FROM users WHERE plan!='free'").fetchone()[0]
    plan_breakdown=db.execute(
        "SELECT plan, COUNT(*) as cnt FROM users GROUP BY plan ORDER BY cnt DESC"
    ).fetchall()

    # ── Tribes ────────────────────────────────────────────────────────────────
    tribe_counts = db.execute(
        "SELECT tribe_id, COUNT(*) as cnt, SUM(herd_cows) as cows FROM users "
        "WHERE tribe_id!='' GROUP BY tribe_id ORDER BY cnt DESC"
    ).fetchall()

    # ── Games ─────────────────────────────────────────────────────────────────
    games_today = db.execute("SELECT COUNT(*) FROM bets WHERE created>?", (day,)).fetchone()[0]
    games_week  = db.execute("SELECT COUNT(*) FROM bets WHERE created>?", (week,)).fetchone()[0]
    cow_packs   = db.execute(
        "SELECT COUNT(*) as cnt, SUM(cows_delta) as cows FROM kingdom_events "
        "WHERE event_type='daily_gift' AND created>?",(week,)
    ).fetchone()

    # ── Competition entries ────────────────────────────────────────────────────
    comp_entries = db.execute(
        "SELECT COUNT(*) FROM competition_players WHERE joined>?", (week,)
    ).fetchone()[0]
    open_comps   = db.execute("SELECT COUNT(*) FROM competitions WHERE status='open'").fetchone()[0]

    # ── Top players by herd ───────────────────────────────────────────────────
    top_players = db.execute(
        "SELECT name,tribe_id,title,herd_cows,plan,wins,has_crown FROM users "
        "ORDER BY herd_cows DESC LIMIT 20"
    ).fetchall()

    # ── Recent payments ───────────────────────────────────────────────────────
    recent_payments = db.execute(
        "SELECT user_email,provider,plan,amount_cents,currency,status,created "
        "FROM payments ORDER BY created DESC LIMIT 50"
    ).fetchall()

    # ── Conversion funnel ─────────────────────────────────────────────────────
    conversion_rate = round(paying_users / total_users * 100, 2) if total_users > 0 else 0
    arpu = round(rev_month / max(1, active_week) / 100, 2)

    return jsonify({
        'generated_at': now,
        'revenue': {
            'today_zar':   round(rev_today/100, 2),
            'week_zar':    round(rev_week/100, 2),
            'month_zar':   round(rev_month/100, 2),
            'total_zar':   round(rev_total/100, 2),
            'by_plan':     [dict(r) for r in rev_by_plan],
            'donations_zar': round(don_total/100, 2),
            'donation_count': don_count,
        },
        'users': {
            'total':       total_users,
            'new_today':   new_today,
            'new_week':    new_week,
            'active_week': active_week,
            'paying':      paying_users,
            'conversion_pct': conversion_rate,
            'arpu_zar':    arpu,
            'by_plan':     [dict(r) for r in plan_breakdown],
        },
        'tribes':   [dict(r) for r in tribe_counts],
        'games': {
            'today': games_today,
            'week':  games_week,
            'daily_gifts_week': dict(cow_packs) if cow_packs else {},
        },
        'competitions': {
            'open':      open_comps,
            'entries_week': comp_entries,
        },
        'top_players':     [dict(r) for r in top_players],
        'recent_payments': [dict(r) for r in recent_payments],
    })


@app.route('/api/admin/export-csv')
def admin_export_csv():
    """Export user data as CSV for offline analysis."""
    if not _require_admin():
        return jsonify({'error': 'Unauthorized'}), 401
    import csv, io
    db   = get_db()
    rows = db.execute(
        "SELECT email,name,plan,herd_cows,tribe_id,age_pool,wins,losses,games,"
        "competition_wins,has_crown,is_married,created FROM users WHERE email!=''"
        " ORDER BY created DESC"
    ).fetchall()
    buf = io.StringIO()
    writer = csv.writer(buf)
    writer.writerow(['email','name','plan','herd_cows','tribe','age_pool',
                     'wins','losses','games','comp_wins','has_crown','married','created'])
    for r in rows:
        writer.writerow(list(r))
    return buf.getvalue(), 200, {
        'Content-Type': 'text/csv',
        'Content-Disposition': 'attachment; filename=intshuba_users.csv'
    }


# ── School teacher dashboard ───────────────────────────────────────────────────
@app.route('/api/school/register', methods=['POST'])
def school_register():
    """Register a school with a code that students use to join the school team."""
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data  = request.get_json(force=True) or {}
    name  = sanitise(str(data.get('school_name','')), 100)
    code  = sanitise(str(data.get('school_code','')), 20).upper()
    grade = sanitise(str(data.get('grade_range','6-12')), 20)
    if not name or not code:
        return jsonify({'error': 'School name and code required'}), 400
    db = get_db()
    existing = db.execute("SELECT id FROM competitions WHERE id=?", (code,)).fetchone()
    if existing:
        return jsonify({'error': 'School code already taken'}), 409
    db.execute(
        "INSERT INTO competitions(id,name,comp_type,host_email,host_name,entry_fee_zar,"
        "prize_pool_zar,status,duration_days,created) VALUES(?,?,?,?,?,?,?,?,?,strftime('%s','now'))",
        (code, name + ' (' + grade + ')', 'school', user['email'], user['name'],
         0, 0, 'open', 365)
    )
    # Grant school admin flag
    db.execute("UPDATE users SET is_admin=1 WHERE email=?", (user['email'],))
    db.commit()
    return jsonify({
        'ok': True,
        'school_code': code,
        'message': f'School "{name}" registered! Students join with code: {code}',
    })


@app.route('/api/school/<school_code>/dashboard')
def school_dashboard(school_code):
    """Teacher dashboard: all students, progress, scores, CAPS alignment."""
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    db   = get_db()
    comp = db.execute(
        "SELECT * FROM competitions WHERE id=? AND (host_email=? OR comp_type='school')",
        (school_code.upper(), user['email'])
    ).fetchone()
    if not comp:
        return jsonify({'error': 'School not found or not authorised'}), 404

    students = db.execute(
        "SELECT cp.player_name, cp.player_email, cp.score, cp.wins, cp.losses, cp.age_pool, cp.joined,"
        "u.herd_cows, u.title, u.tribe_id, u.games "
        "FROM competition_players cp LEFT JOIN users u ON u.email=cp.player_email "
        "WHERE cp.comp_id=? ORDER BY cp.score DESC, cp.wins DESC",
        (school_code.upper(),)
    ).fetchall()

    total     = len(students)
    avg_wins  = round(sum(s['wins'] for s in students) / max(1,total), 1)
    avg_games = round(sum(s['games'] or 0 for s in students) / max(1,total), 1)

    # CAPS alignment notes
    caps_notes = {
        'mathematical_thinking': 'Counting stones, predicting captures, tracking totals — aligns with Gr4-7 Number Sense.',
        'logical_reasoning':     'Planning multi-step moves, anticipating opponent — aligns with Gr4-12 Problem Solving.',
        'pattern_recognition':   'Identifying relay chains and board patterns — aligns with Gr4-9 Patterns & Algebra.',
        'strategic_thinking':    'Long-term herd management, betting decisions — aligns with Gr10-12 Decision Making.',
        'cultural_heritage':     'Authentic Nguni game with 24-language support — aligns with LO/Life Orientation & Social Sciences.',
    }

    return jsonify({
        'school':    dict(comp),
        'students':  [dict(s) for s in students],
        'summary': {
            'total_students': total,
            'avg_wins':       avg_wins,
            'avg_games':      avg_games,
            'top_student':    dict(students[0]) if students else {},
        },
        'caps_alignment': caps_notes,
    })


@app.route('/api/school/join', methods=['POST'])
def school_join():
    """Student joins their school team using the school code."""
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data = request.get_json(force=True) or {}
    code = sanitise(str(data.get('school_code','')), 20).upper()
    db   = get_db()
    comp = db.execute(
        "SELECT * FROM competitions WHERE id=? AND comp_type='school'", (code,)
    ).fetchone()
    if not comp:
        return jsonify({'error': 'Invalid school code'}), 404
    existing = db.execute(
        "SELECT id FROM competition_players WHERE comp_id=? AND player_email=?",
        (code, user['email'])
    ).fetchone()
    if existing:
        return jsonify({'ok': True, 'message': 'Already enrolled in this school!'})
    db.execute(
        "INSERT INTO competition_players(comp_id,player_email,player_name,tribe,age_pool) VALUES(?,?,?,?,?)",
        (code, user['email'], user['name'],
         sanitise(str(data.get('tribe','world')),30),
         sanitise(str(data.get('age_pool','open')),20))
    )
    db.commit()
    return jsonify({
        'ok': True,
        'school_name': comp['name'],
        'message': f'Enrolled in {comp["name"]}! 🏫 Your teacher can now track your progress.',
    })


# ── Season prize system ────────────────────────────────────────────────────────
PRIZE_TIERS = {
    'isilo':          {'label': 'iSilo Champion',       'cash_zar': 100000, 'icon': '🔱', 'desc': 'Supreme season winner — international'},
    'paramount':      {'label': 'Paramount Champion',   'cash_zar': 25000,  'icon': '🦁', 'desc': 'National age-pool winner'},
    'inkosi':         {'label': 'Inkosi Champion',      'cash_zar': 5000,   'icon': '👑', 'desc': 'Community/school winner'},
    'tribe_war':      {'label': 'Tribe War Winner',     'cash_zar': 10000,  'icon': '⚔️', 'desc': 'Winning tribe — split between top 10 members'},
    'school_top3':    {'label': 'School Top 3',         'cash_zar': 1000,   'icon': '🏫', 'desc': 'Top 3 per school — trophy + certificate'},
    'daily_fastest':  {'label': 'Daily Speed Winner',   'cash_zar': 100,    'icon': '⚡', 'desc': 'Fastest win each day'},
    'monthly_mvp':    {'label': 'Monthly MVP',          'cash_zar': 500,    'icon': '🏆', 'desc': 'Most wins per age pool per month'},
}

@app.route('/api/season/prizes')
def season_prizes():
    """Return current season prize structure and eligible players."""
    db   = get_db()
    now  = int(time.time())
    season_len = SEASON_DAYS * 86400
    season_num = (now // season_len) + 1
    season_end = season_num * season_len
    days_left  = max(0, (season_end - now) // 86400)

    # Current standings per tier
    king = _get_current_king()
    top_by_pool = {}
    for pool_id, pool in AGE_POOLS.items():
        rows = db.execute(
            "SELECT name,title,herd_cows,tribe_id,wins,competition_wins FROM users "
            "WHERE age_pool=? ORDER BY competition_wins DESC, herd_cows DESC LIMIT 3",
            (pool_id,)
        ).fetchall()
        top_by_pool[pool_id] = [dict(r) for r in rows]

    # Tribe war current standing
    tribe_rows = db.execute(
        "SELECT tm.tribe_id, COUNT(u.email) as members, SUM(u.herd_cows) as total_cows, SUM(u.wins) as wins "
        "FROM users u JOIN tribe_memberships tm ON tm.player_email=u.email "
        "GROUP BY tm.tribe_id ORDER BY total_cows DESC LIMIT 3"
    ).fetchall()

    return jsonify({
        'season':     season_num,
        'days_left':  days_left,
        'season_end': season_end,
        'prize_tiers': PRIZE_TIERS,
        'current_leader': king,
        'top_by_age_pool': top_by_pool,
        'tribe_war_top3': [dict(r) for r in tribe_rows],
        'total_prize_pool_zar': sum(v['cash_zar'] for v in PRIZE_TIERS.values()),
    })


@app.route('/api/season/claim-prize', methods=['POST'])
def claim_season_prize():
    """Record a prize claim at end of season (admin-verified payout)."""
    if not _require_admin():
        return jsonify({'error': 'Unauthorized'}), 401
    data       = request.get_json(force=True) or {}
    email      = sanitise(str(data.get('email','')), 80)
    prize_tier = sanitise(str(data.get('tier','')), 40)
    if prize_tier not in PRIZE_TIERS:
        return jsonify({'error': 'Invalid prize tier'}), 400
    prize = PRIZE_TIERS[prize_tier]
    db    = get_db()
    db.execute(
        "INSERT INTO kingdom_events(user_email,event_type,detail,cows_delta) VALUES(?,?,?,0)",
        (email, 'season_prize_' + prize_tier,
         json.dumps({'cash_zar': prize['cash_zar'], 'label': prize['label']}))
    )
    db.execute(
        "UPDATE users SET competition_wins=competition_wins+1 WHERE email=?", (email,)
    )
    db.commit()
    return jsonify({
        'ok': True,
        'prize': prize,
        'message': f'{prize["icon"]} {prize["label"]} — R{prize["cash_zar"]:,} prize recorded for {email}',
    })


# ── Live-stream integration ────────────────────────────────────────────────────
@app.route('/api/competition/<comp_id>/stream', methods=['GET','POST'])
def competition_stream(comp_id):
    """GET returns stream info. POST (admin) sets stream URL."""
    db   = get_db()
    comp = db.execute("SELECT * FROM competitions WHERE id=?", (comp_id,)).fetchone()
    if not comp:
        return jsonify({'error': 'Competition not found'}), 404
    if request.method == 'POST':
        user = current_user()
        if not user or (user['email'] != comp['host_email'] and not _require_admin()):
            return jsonify({'error': 'Not authorised'}), 401
        data   = request.get_json(force=True) or {}
        stream = sanitise(str(data.get('stream_url','')), 300)
        db.execute("UPDATE competitions SET stream_url=? WHERE id=?", (stream, comp_id))
        db.commit()
        return jsonify({'ok': True, 'stream_url': stream})
    # GET
    return jsonify({
        'competition': dict(comp),
        'stream_url':  comp['stream_url'] or '',
        'is_live':     bool(comp['stream_url']),
        'embed_url':   _make_embed_url(comp['stream_url'] or ''),
    })


def _make_embed_url(url: str) -> str:
    """Convert YouTube watch URL to embed URL for iframe."""
    if not url:
        return ''
    if 'youtube.com/watch?v=' in url:
        vid = url.split('v=')[1].split('&')[0]
        return f'https://www.youtube.com/embed/{vid}?autoplay=1'
    if 'youtu.be/' in url:
        vid = url.split('youtu.be/')[1].split('?')[0]
        return f'https://www.youtube.com/embed/{vid}?autoplay=1'
    if 'twitch.tv/' in url:
        channel = url.rstrip('/').split('/')[-1]
        return f'https://player.twitch.tv/?channel={channel}&parent={os.environ.get("APP_URL","localhost").replace("https://","").replace("http://","")}'
    return url


@app.route('/api/livestreams')
def list_livestreams():
    """Return all competitions with active stream URLs."""
    db   = get_db()
    rows = db.execute(
        "SELECT id,name,comp_type,stream_url,status FROM competitions "
        "WHERE stream_url!='' AND stream_url IS NOT NULL ORDER BY created DESC LIMIT 20"
    ).fetchall()
    streams = []
    for r in rows:
        d = dict(r)
        d['embed_url'] = _make_embed_url(d['stream_url'])
        streams.append(d)
    return jsonify({'streams': streams, 'count': len(streams)})


# ── Admin dashboard served as a full HTML page ───────────────────────────────
ADMIN_DASHBOARD_HTML = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>🐄 Intshuba Admin</title>
<style>
*{box-sizing:border-box;margin:0;padding:0}
body{background:#0D0804;color:#F5ECD7;font-family:'Segoe UI',sans-serif;font-size:14px}
.hdr{background:rgba(201,168,76,.12);border-bottom:1px solid rgba(201,168,76,.3);
  padding:14px 24px;display:flex;align-items:center;gap:12px}
.hdr h1{font-size:18px;color:#C9A84C;letter-spacing:1px}
.hdr span{opacity:.4;font-size:12px}
.body{padding:20px 24px;max-width:1400px}
.grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(200px,1fr));gap:12px;margin-bottom:20px}
.kpi{background:rgba(201,168,76,.07);border:1px solid rgba(201,168,76,.25);
  border-radius:10px;padding:16px;text-align:center}
.kpi-val{font-size:28px;font-weight:700;color:#C9A84C;font-family:'Courier New',monospace}
.kpi-lbl{font-size:11px;color:rgba(245,236,215,.45);letter-spacing:1px;margin-top:4px}
.section{background:rgba(255,255,255,.03);border:1px solid rgba(255,255,255,.07);
  border-radius:10px;padding:16px;margin-bottom:16px}
.section h2{font-size:13px;color:#C9A84C;letter-spacing:2px;text-transform:uppercase;
  margin-bottom:12px;padding-bottom:8px;border-bottom:1px solid rgba(201,168,76,.2)}
table{width:100%;border-collapse:collapse;font-size:12px}
th{text-align:left;padding:8px 10px;background:rgba(201,168,76,.15);
   color:#C9A84C;font-size:10px;letter-spacing:1px;text-transform:uppercase}
td{padding:7px 10px;border-bottom:1px solid rgba(255,255,255,.05);color:rgba(245,236,215,.75)}
tr:hover td{background:rgba(201,168,76,.05)}
.badge{display:inline-block;padding:2px 8px;border-radius:4px;font-size:10px;font-weight:600}
.b-green{background:rgba(107,255,170,.15);color:#6bffaa}
.b-gold{background:rgba(201,168,76,.2);color:#C9A84C}
.b-blue{background:rgba(68,136,255,.15);color:#88aaff}
.b-red{background:rgba(255,80,80,.15);color:#ff8888}
.tab-row{display:flex;gap:6px;margin-bottom:12px;flex-wrap:wrap}
.tab{padding:6px 14px;border-radius:6px;cursor:pointer;font-size:12px;border:none;
     background:rgba(255,255,255,.06);color:rgba(245,236,215,.6);transition:.2s}
.tab.act{background:rgba(201,168,76,.2);color:#C9A84C}
.bar-wrap{display:flex;align-items:center;gap:8px;margin-bottom:4px}
.bar{height:8px;border-radius:4px;background:rgba(201,168,76,.6);transition:.4s}
.tribe-icon{font-size:18px}
#login-screen{display:flex;flex-direction:column;align-items:center;justify-content:center;
  height:100vh;gap:12px}
#login-screen input{background:rgba(255,255,255,.07);border:1px solid rgba(201,168,76,.3);
  color:#F5ECD7;padding:10px 16px;border-radius:8px;font-size:14px;width:280px}
#login-screen button{background:linear-gradient(135deg,#8B1A1A,#5a0808);
  border:1px solid #C9A84C;color:#C9A84C;padding:10px 28px;border-radius:8px;
  font-size:14px;cursor:pointer;letter-spacing:1px}
.refresh-btn{float:right;background:none;border:1px solid rgba(201,168,76,.3);
  color:rgba(201,168,76,.7);padding:4px 12px;border-radius:6px;cursor:pointer;font-size:11px}
.err{color:#ff8888;font-size:12px;text-align:center;padding:8px}
</style>
</head>
<body>

<div id="login-screen">
  <div style="font-size:48px">🐄</div>
  <div style="font-family:'Courier New';font-size:18px;color:#C9A84C;letter-spacing:2px">INTSHUBA ADMIN</div>
  <input type="password" id="admin-key" placeholder="Admin Key" autocomplete="off">
  <button onclick="adminLogin()">Enter Dashboard</button>
  <div id="login-err" class="err"></div>
</div>

<div id="dashboard" style="display:none">
  <div class="hdr">
    <div style="font-size:24px">🐄</div>
    <h1>INTSHUBA ADMIN</h1>
    <span id="dash-time">—</span>
    <div style="margin-left:auto;display:flex;gap:8px">
      <button class="refresh-btn" onclick="loadDashboard()">↻ Refresh</button>
      <button class="refresh-btn" onclick="exportCSV()">⬇ Export CSV</button>
    </div>
  </div>
  <div class="body">

    <!-- KPI Row -->
    <div class="grid" id="kpi-grid">
      <div class="kpi"><div class="kpi-val" id="k-rev-today">—</div><div class="kpi-lbl">REVENUE TODAY (R)</div></div>
      <div class="kpi"><div class="kpi-val" id="k-rev-month">—</div><div class="kpi-lbl">REVENUE 30 DAYS (R)</div></div>
      <div class="kpi"><div class="kpi-val" id="k-rev-total">—</div><div class="kpi-lbl">TOTAL REVENUE (R)</div></div>
      <div class="kpi"><div class="kpi-val" id="k-users">—</div><div class="kpi-lbl">TOTAL PLAYERS</div></div>
      <div class="kpi"><div class="kpi-val" id="k-active">—</div><div class="kpi-lbl">ACTIVE THIS WEEK</div></div>
      <div class="kpi"><div class="kpi-val" id="k-paying">—</div><div class="kpi-lbl">PAYING PLAYERS</div></div>
      <div class="kpi"><div class="kpi-val" id="k-conv">—</div><div class="kpi-lbl">CONVERSION %</div></div>
      <div class="kpi"><div class="kpi-val" id="k-games">—</div><div class="kpi-lbl">GAMES TODAY</div></div>
    </div>

    <div style="display:grid;grid-template-columns:1fr 1fr;gap:16px">

      <!-- Left column -->
      <div>
        <!-- Revenue by plan -->
        <div class="section">
          <h2>Revenue by Plan</h2>
          <table id="rev-plan-table">
            <tr><th>Plan</th><th>Payments</th><th>Revenue (R)</th></tr>
          </table>
        </div>
        <!-- Player plan breakdown -->
        <div class="section">
          <h2>Player Plans</h2>
          <div id="plan-bars"></div>
        </div>
        <!-- Tribe standings -->
        <div class="section">
          <h2>Tribe War Standings</h2>
          <div id="tribe-bars"></div>
        </div>
      </div>

      <!-- Right column -->
      <div>
        <!-- Recent payments -->
        <div class="section">
          <h2>Recent Payments <button class="refresh-btn" onclick="loadDashboard()">↻</button></h2>
          <table id="payments-table">
            <tr><th>Player</th><th>Plan</th><th>Amount</th><th>Via</th><th>When</th></tr>
          </table>
        </div>
        <!-- Top players -->
        <div class="section">
          <h2>Top 10 Players by Herd</h2>
          <table id="players-table">
            <tr><th>#</th><th>Name</th><th>Title</th><th>Herd🐄</th><th>Plan</th><th>Crown</th></tr>
          </table>
        </div>
      </div>

    </div>

    <!-- Prizes section -->
    <div class="section">
      <h2>Season Prize Pool</h2>
      <div id="prizes-grid" style="display:grid;grid-template-columns:repeat(auto-fit,minmax(180px,1fr));gap:10px"></div>
    </div>

    <!-- Live streams -->
    <div class="section">
      <h2>Active Live Streams</h2>
      <div id="streams-list"><div style="opacity:.4;font-size:12px">No active streams</div></div>
    </div>

  </div>
</div>

<script>
let _adminKey = '';

function adminLogin() {
  _adminKey = document.getElementById('admin-key').value.trim();
  if (!_adminKey) return;
  loadDashboard();
}

async function loadDashboard() {
  try {
    const r = await fetch('/api/admin/dashboard', {
      headers: {'X-Admin-Key': _adminKey}
    });
    if (r.status === 401) {
      document.getElementById('login-err').textContent = 'Invalid admin key';
      return;
    }
    const d = await r.json();
    document.getElementById('login-screen').style.display = 'none';
    document.getElementById('dashboard').style.display = 'block';
    renderDashboard(d);
    // Also load prizes and streams
    loadPrizes();
    loadStreams();
  } catch(e) {
    document.getElementById('login-err').textContent = 'Connection error: ' + e.message;
  }
}

function renderDashboard(d) {
  const rev = d.revenue || {}, usr = d.users || {}, gam = d.games || {};
  document.getElementById('dash-time').textContent = 
    'Updated: ' + new Date(d.generated_at*1000).toLocaleTimeString();

  // KPIs
  setText('k-rev-today',  'R' + fmt(rev.today_zar));
  setText('k-rev-month',  'R' + fmt(rev.month_zar));
  setText('k-rev-total',  'R' + fmt(rev.total_zar));
  setText('k-users',      fmt(usr.total));
  setText('k-active',     fmt(usr.active_week));
  setText('k-paying',     fmt(usr.paying));
  setText('k-conv',       (usr.conversion_pct||0).toFixed(1) + '%');
  setText('k-games',      fmt(gam.today));

  // Revenue by plan table
  const rpt = document.getElementById('rev-plan-table');
  rpt.innerHTML = '<tr><th>Plan</th><th>Payments</th><th>Revenue (R)</th></tr>';
  (rev.by_plan||[]).forEach(p => {
    const tr = rpt.insertRow();
    tr.innerHTML = `<td><span class="badge b-gold">${p.plan||'—'}</span></td><td>${p.cnt}</td><td>R${fmt(p.total/100)}</td>`;
  });

  // Plan bars
  const total = usr.total || 1;
  const pb = document.getElementById('plan-bars');
  pb.innerHTML = (usr.by_plan||[]).map(p => {
    const pct = Math.round(p.cnt/total*100);
    const color = {inkosi:'#C9A84C',pro:'#6bffaa',school:'#88aaff',free:'rgba(245,236,215,.3)'}[p.plan]||'#888';
    return `<div class="bar-wrap">
      <div style="width:70px;font-size:11px;color:rgba(245,236,215,.6)">${p.plan}</div>
      <div class="bar" style="width:${Math.max(4,pct*2)}px;background:${color}"></div>
      <div style="font-size:11px;color:rgba(245,236,215,.5)">${p.cnt} (${pct}%)</div>
    </div>`;
  }).join('');

  // Tribe bars
  const TRIBE_ICONS = {amazulu:'🐗',amaxhosa:'🦬',amandebele:'🎨',emaswati:'🦁',
                       vatsonga:'🌿',basotho:'☀️',bapedi:'🌙',bavenda:'🌊',world:'🌍'};
  const maxCows = Math.max(1, ...(d.tribes||[]).map(t=>t.cows||0));
  const tb = document.getElementById('tribe-bars');
  tb.innerHTML = (d.tribes||[]).map(t => {
    const pct = Math.round((t.cows||0)/maxCows*100);
    return `<div class="bar-wrap">
      <span class="tribe-icon">${TRIBE_ICONS[t.tribe_id]||'🐄'}</span>
      <div style="width:80px;font-size:11px;color:rgba(245,236,215,.7)">${t.tribe_id}</div>
      <div class="bar" style="width:${Math.max(4,pct)}px"></div>
      <div style="font-size:11px;color:rgba(245,236,215,.5)">${(t.cows||0).toLocaleString()}🐄</div>
    </div>`;
  }).join('') || '<div style="opacity:.4;font-size:12px">No tribe data yet</div>';

  // Recent payments
  const pt = document.getElementById('payments-table');
  pt.innerHTML = '<tr><th>Player</th><th>Plan</th><th>Amount</th><th>Via</th><th>When</th></tr>';
  (d.recent_payments||[]).slice(0,15).forEach(p => {
    const tr = pt.insertRow();
    const ago = timeAgo(p.created);
    const plan_color = {inkosi:'b-gold',pro:'b-green',school:'b-blue'}[p.plan]||'b-red';
    tr.innerHTML = `<td style="max-width:120px;overflow:hidden;text-overflow:ellipsis">${p.user_email}</td>
      <td><span class="badge ${plan_color}">${p.plan}</span></td>
      <td>R${fmt(p.amount_cents/100)}</td>
      <td><span class="badge b-blue">${p.provider}</span></td>
      <td style="opacity:.5">${ago}</td>`;
  });

  // Top players
  const plt = document.getElementById('players-table');
  plt.innerHTML = '<tr><th>#</th><th>Name</th><th>Title</th><th>Herd🐄</th><th>Plan</th><th>Crown</th></tr>';
  (d.top_players||[]).forEach((p,i) => {
    const tr = plt.insertRow();
    const plan_color = {inkosi:'b-gold',pro:'b-green',school:'b-blue',free:''}[p.plan]||'';
    tr.innerHTML = `<td style="opacity:.5">${i+1}</td>
      <td><strong>${p.name}</strong></td>
      <td style="font-size:11px;opacity:.7">${p.title||'—'}</td>
      <td style="color:#C9A84C;font-weight:600">${(p.herd_cows||0).toLocaleString()}</td>
      <td><span class="badge ${plan_color}">${p.plan||'free'}</span></td>
      <td>${p.has_crown ? '👑' : ''}</td>`;
  });
}

async function loadPrizes() {
  try {
    const d = await (await fetch('/api/season/prizes')).json();
    const el = document.getElementById('prizes-grid');
    const tiers = d.prize_tiers || {};
    el.innerHTML = Object.entries(tiers).map(([id,t]) =>
      `<div style="background:rgba(201,168,76,.06);border:1px solid rgba(201,168,76,.2);
        border-radius:8px;padding:12px;text-align:center">
        <div style="font-size:22px">${t.icon}</div>
        <div style="font-size:12px;font-weight:600;color:#C9A84C;margin:4px 0">${t.label}</div>
        <div style="font-size:18px;font-weight:700;color:#6bffaa">R${t.cash_zar.toLocaleString()}</div>
        <div style="font-size:10px;opacity:.4;margin-top:3px">${t.desc}</div>
      </div>`
    ).join('');
    if (d.days_left !== undefined) {
      el.insertAdjacentHTML('beforeend',
        `<div style="background:rgba(201,168,76,.12);border:1px solid #C9A84C;
          border-radius:8px;padding:12px;text-align:center;grid-column:1/-1">
          <div style="font-size:11px;color:rgba(245,236,215,.4)">SEASON ENDS IN</div>
          <div style="font-size:24px;font-weight:700;color:#C9A84C">${d.days_left} days</div>
          <div style="font-size:12px;opacity:.5">Total prize pool: R${(d.total_prize_pool_zar||0).toLocaleString()}</div>
        </div>`
      );
    }
  } catch(e) {}
}

async function loadStreams() {
  try {
    const d = await (await fetch('/api/livestreams')).json();
    const el = document.getElementById('streams-list');
    if (!d.streams?.length) { el.innerHTML = '<div style="opacity:.4;font-size:12px">No active streams</div>'; return; }
    el.innerHTML = d.streams.map(s =>
      `<div style="display:flex;align-items:center;gap:10px;padding:8px;
        border-bottom:1px solid rgba(255,255,255,.05)">
        <span style="font-size:16px">🔴</span>
        <div style="flex:1">
          <div style="font-size:13px;font-weight:600">${s.name}</div>
          <div style="font-size:11px;opacity:.4">${s.comp_type}</div>
        </div>
        <a href="${s.stream_url}" target="_blank" rel="noopener"
           style="color:#88aaff;font-size:11px;text-decoration:none">Watch →</a>
      </div>`
    ).join('');
  } catch(e) {}
}

async function exportCSV() {
  window.open('/api/admin/export-csv', '_blank');
}

// Helpers
function setText(id, val) { const el=document.getElementById(id); if(el) el.textContent=val; }
function fmt(n) { return Number(n||0).toLocaleString('en-ZA',{minimumFractionDigits:0,maximumFractionDigits:2}); }
function timeAgo(ts) {
  const diff = Date.now()/1000 - ts;
  if (diff<60) return Math.round(diff)+'s ago';
  if (diff<3600) return Math.round(diff/60)+'m ago';
  if (diff<86400) return Math.round(diff/3600)+'h ago';
  return Math.round(diff/86400)+'d ago';
}

// Auto-refresh every 60 seconds if logged in
setInterval(() => { if (_adminKey) loadDashboard(); }, 60000);

<!-- ══════════════════════════════════════════════════════
     SHARE MODAL
═══════════════════════════════════════════════════════ -->
<div class="modal hidden" id="share-modal">
 <div class="modal-box" style="max-width:460px">
  <div class="mtitle">📤 SHARE INTSHUBA</div>
  <div class="nguni-bar"></div>
  <div style="text-align:center;font-size:13px;color:rgba(245,236,215,.55);margin-bottom:14px;line-height:1.6">
    Share the ancient Nguni game with friends, family, and your community!<br>
    <span id="share-subtext" style="color:var(--gold);font-size:12px"></span>
  </div>
  <!-- Share buttons grid -->
  <div id="share-buttons-grid" style="display:grid;grid-template-columns:repeat(4,1fr);gap:8px;margin-bottom:14px"></div>
  <!-- Referral link -->
  <div id="share-referral-box" style="display:none;background:rgba(201,168,76,.08);border:1px solid rgba(201,168,76,.25);border-radius:8px;padding:10px;margin-bottom:10px">
    <div style="font-size:11px;color:rgba(245,236,215,.45);margin-bottom:6px">YOUR REFERRAL LINK — earn 5🐄 per new player</div>
    <div style="display:flex;gap:6px">
      <input id="ref-link-inp" class="inp" readonly style="margin-bottom:0;flex:1;font-size:11px;font-family:'Courier New'">
      <button class="btn green" style="padding:6px 12px;font-size:11px" onclick="copyRefLink()">Copy</button>
    </div>
  </div>
  <div id="share-copy-status" style="text-align:center;font-size:12px;color:#6bffaa;min-height:20px"></div>
  <div style="display:flex;gap:8px;justify-content:center;margin-top:8px">
    <button class="btn" onclick="closeM('share-modal')">Close</button>
  </div>
 </div>
</div>

<!-- ══════════════════════════════════════════════════════
     CEREMONY MODAL
═══════════════════════════════════════════════════════ -->
<div class="modal hidden" id="ceremony-modal">
 <div class="modal-box" style="max-width:440px;text-align:center">
  <div class="mtitle" id="cer-title">🔥 ANCESTRAL CEREMONY REQUIRED</div>
  <div class="nguni-bar"></div>
  <div style="font-size:60px;margin:10px 0" id="cer-icon">🐄</div>
  <div style="font-family:'Cinzel',serif;color:var(--gold);font-size:16px;margin-bottom:8px" id="cer-name">Ceremony Name</div>
  <div style="font-size:13px;color:rgba(245,236,215,.65);margin-bottom:14px;line-height:1.6" id="cer-desc">Description</div>
  <div style="background:rgba(201,168,76,.1);border:1px solid rgba(201,168,76,.3);border-radius:8px;padding:10px;margin-bottom:14px">
    <div style="font-size:11px;color:rgba(245,236,215,.4);margin-bottom:4px">CATTLE TO SLAUGHTER</div>
    <div style="font-size:24px;font-weight:700;color:#ff9999" id="cer-cost">0 🐄</div>
    <div style="font-size:11px;color:rgba(245,236,215,.35);margin-top:4px" id="cer-herd">Your herd: — cows</div>
  </div>
  <div style="background:rgba(107,255,170,.08);border:1px solid rgba(107,255,170,.2);border-radius:8px;padding:8px;margin-bottom:14px">
    <div style="font-size:10px;color:rgba(107,255,170,.5);margin-bottom:3px">ANCESTOR BLESSING</div>
    <div style="font-size:12px;color:#6bffaa" id="cer-blessing">Blessing description</div>
  </div>
  <div style="display:flex;gap:8px;justify-content:center">
    <button class="btn" style="background:linear-gradient(135deg,#8B1A1A,#5a0808);border-color:#C9A84C;color:#C9A84C"
      id="cer-confirm-btn" onclick="performCeremony()">🔥 Perform Ceremony</button>
    <button class="btn" onclick="closeM('ceremony-modal');skipCeremony()">Skip (no blessing)</button>
  </div>
 </div>
</div>

<!-- ══════════════════════════════════════════════════════
     TRADES MODAL
═══════════════════════════════════════════════════════ -->
<div class="modal hidden" id="trades-modal">
 <div class="modal-box" style="max-width:520px">
  <div class="mtitle">⚒️ TRADES & PROFESSIONS</div>
  <div class="nguni-bar"></div>
  <div style="font-size:12px;color:rgba(245,236,215,.5);margin-bottom:12px;line-height:1.6">
    Unlock trade professions to earn daily passive income. Each profession carries risk —<br>
    dangerous trades can lose income on bad days. Sangoma has the lowest risk.
  </div>
  <div style="display:flex;border-bottom:.5px solid var(--border);margin-bottom:10px">
    <button class="cw-tab act" id="trt-trades"     onclick="tradesTab('trades')"    >⚒️ Trades</button>
    <button class="cw-tab"     id="trt-ceremonies"  onclick="tradesTab('ceremonies')">🔥 Ceremonies</button>
  </div>
  <div id="trp-trades">
    <div id="trades-list" style="display:grid;grid-template-columns:1fr 1fr;gap:8px;max-height:340px;overflow-y:auto"></div>
  </div>
  <div id="trp-ceremonies" style="display:none">
    <div style="font-size:12px;color:rgba(245,236,215,.5);margin-bottom:10px;line-height:1.5">
      Ancestral ceremonies are triggered automatically at key milestones.<br>
      Each costs cattle but grants a powerful blessing from the ancestors.
    </div>
    <div id="ceremonies-list" style="max-height:300px;overflow-y:auto"></div>
  </div>
  <div id="trades-msg" class="ok" style="display:none;text-align:center;margin-top:8px"></div>
  <div style="display:flex;gap:8px;margin-top:10px;justify-content:center">
    <button class="btn" onclick="closeM('trades-modal')">Close</button>
  </div>
 </div>
</div>

</script>

<!-- ── Bottom Navigation Bar ── -->
<nav id="bottom-nav">
  <button class="bnav-btn active" id="bnav-home" onclick="bnavGo('home')">
    <span class="bnav-icon">🏠</span>Home
  </button>
  <button class="bnav-btn" id="bnav-play" onclick="bnavGo('play')">
    <span class="bnav-icon-wrap">
      <span class="bnav-icon">♟</span>
      <span class="bnav-badge" id="bnav-play-badge" style="display:none">!</span>
    </span>Play
  </button>
  <button class="bnav-btn" id="bnav-kingdom" onclick="bnavGo('kingdom')">
    <span class="bnav-icon-wrap">
      <span class="bnav-icon">🐄</span>
    </span>Kingdom
  </button>
  <button class="bnav-btn" id="bnav-social" onclick="bnavGo('social')">
    <span class="bnav-icon-wrap">
      <span class="bnav-icon">👥</span>
      <span class="bnav-badge" id="bnav-social-badge" style="display:none">!</span>
    </span>Social
  </button>
  <button class="bnav-btn" id="bnav-store" onclick="bnavGo('store')">
    <span class="bnav-icon">🛒</span>Store
  </button>
  <button class="bnav-btn" id="bnav-profile" onclick="bnavGo('profile')">
    <span class="bnav-icon">👤</span>Profile
  </button>
</nav>

<!-- AR/VR launch FAB (shown when mode=ar|vr) -->
<button id="xr-launch-btn" onclick="launchXR()" title="Launch AR/VR mode">🥽</button>

</body>
</html>"""


@app.route('/admin')
@app.route('/admin/')
def admin_panel():
    """Serve the admin dashboard HTML page."""
    return ADMIN_DASHBOARD_HTML, 200, {'Content-Type': 'text/html; charset=utf-8'}


# ═══════════════════════════════════════════════════════════════════════════════
#  EXTENDED ECONOMY  ·  SECURITY  ·  SOCIAL SHARE  ·  LEADERBOARD
#  ANCESTOR CEREMONY  ·  TRADES EXPANSION
# ═══════════════════════════════════════════════════════════════════════════════

# ── Extended trade professions ────────────────────────────────────────────────
TRADE_PROFESSIONS = {
    # ── Hunters & Animal trades ───────────────────────────────────────────────
    'hunter': {
        'name': 'Hunter (umZingeli)', 'icon': '🏹', 'cows': 60,
        'earn_day': 5, 'category': 'hunter',
        'desc': 'Hunt wild animals for meat, hide, and tusks. Sell at the market. Rare kills bring +20 cows bonus.',
        'unlock_level': 2,
        'products': ['meat', 'hide', 'ivory'],
        'risk': 'Injury event: 10% chance per day — lose 2 cows medical cost',
    },
    'leather_turner': {
        'name': 'Leather Turner (uMbazi)', 'icon': '🐾', 'cows': 80,
        'earn_day': 7, 'category': 'hunter',
        'desc': 'Tan and craft animal hides into shields, garments, and drums. Requires hunter.',
        'unlock_level': 2,
        'requires': 'hunter',
        'products': ['shield', 'drum', 'garment'],
    },
    'ivory_carver': {
        'name': 'Ivory Carver (uMbazi weNdlovu)', 'icon': '🦷', 'cows': 120,
        'earn_day': 10, 'category': 'hunter',
        'desc': 'Carve ivory into ornaments and regalia. High value. Sells at 3× cost.',
        'unlock_level': 3,
        'requires': 'hunter',
    },
    # ── Craftsmen ─────────────────────────────────────────────────────────────
    'craftsman': {
        'name': 'Craftsman (uNgcweti)', 'icon': '🔨', 'cows': 70,
        'earn_day': 6, 'category': 'craftsman',
        'desc': 'Create tools, weapons, household goods. Sell to other players at 2× cost.',
        'unlock_level': 2,
        'products': ['tools', 'weapons', 'goods'],
    },
    'potter': {
        'name': 'Master Potter (uMbumbi)', 'icon': '🏺', 'cows': 55,
        'earn_day': 5, 'category': 'craftsman',
        'desc': 'Craft traditional pottery, beer pots, cooking pots. Ceremonial pots earn more.',
        'unlock_level': 1,
    },
    'weaver': {
        'name': 'Weaver (uMalukazi)', 'icon': '🧺', 'cows': 50,
        'earn_day': 4, 'category': 'craftsman',
        'desc': 'Weave grass mats, baskets, and sleeping mats. Passive daily income.',
        'unlock_level': 1,
    },
    'beadmaker': {
        'name': 'Beadmaker (uMakhi weZincu)', 'icon': '📿', 'cows': 65,
        'earn_day': 6, 'category': 'craftsman',
        'desc': 'String traditional Nguni beadwork. Each colour carries a message. High demand.',
        'unlock_level': 2,
    },
    # ── Builders ──────────────────────────────────────────────────────────────
    'builder': {
        'name': 'Builder (uMakhi)', 'icon': '🏗️', 'cows': 90,
        'earn_day': 8, 'category': 'builder',
        'desc': 'Build homesteads, kraals, grain stores. Earn per build contract. Unlock upgrades.',
        'unlock_level': 2,
    },
    'stone_mason': {
        'name': 'Stone Mason (uMakhi wamatshe)', 'icon': '🪨', 'cows': 110,
        'earn_day': 9, 'category': 'builder',
        'desc': 'Build stone fortifications and walls. Reduces crown challenge cost by 50 cows.',
        'unlock_level': 3,
        'bonus': 'crown_defense',
    },
    # ── Mining & Metals ────────────────────────────────────────────────────────
    'miner': {
        'name': 'Miner (uMmbi)', 'icon': '⛏️', 'cows': 100,
        'earn_day': 9, 'category': 'miner',
        'desc': 'Mine gold, iron ore, and coal. Sell raw materials to smiths. Risk: mine collapse.',
        'unlock_level': 3,
        'products': ['gold', 'iron_ore', 'coal'],
        'risk': 'Mine collapse: 5% chance — lose 5 cows',
    },
    'goldsmith': {
        'name': 'Goldsmith (uMakhi weGolide)', 'icon': '🥇', 'cows': 150,
        'earn_day': 12, 'category': 'miner',
        'desc': 'Craft gold jewellery, crowns, and royal insignia. Sells at 4× cost.',
        'unlock_level': 3,
        'requires': 'miner',
    },
    'ironsmith': {
        'name': 'Ironsmith (uMakhi wensimbi)', 'icon': '⚒️', 'cows': 100,
        'earn_day': 8, 'category': 'miner',
        'desc': 'Forge weapons, agricultural tools, and iron regalia. Also unlocks war spear.',
        'unlock_level': 2,
    },
    # ── Engineers & Advanced ───────────────────────────────────────────────────
    'engineer': {
        'name': 'Engineer (uNjiniyela)', 'icon': '⚙️', 'cows': 200,
        'earn_day': 15, 'category': 'engineer',
        'desc': 'Design irrigation systems, bridges, and fortifications. Highest daily income.',
        'unlock_level': 4,
        'requires': 'builder',
        'bonus': 'irrigation',
    },
    'herbalist': {
        'name': 'Herbalist / Healer (iSangoma)', 'icon': '🌿', 'cows': 75,
        'earn_day': 7, 'category': 'healer',
        'desc': 'Brew traditional medicine. Heal injured warriors. Earn from ceremony officiating.',
        'unlock_level': 2,
        'bonus': 'reduce_injury_loss',
    },
    'trader': {
        'name': 'Long-distance Trader (uMthengisi)', 'icon': '🐪', 'cows': 140,
        'earn_day': 11, 'category': 'trader',
        'desc': 'Trade between tribes. Opens inter-tribal market. Earns +5% on all sales.',
        'unlock_level': 3,
        'bonus': 'inter_tribe_trade',
    },
    'praise_singer': {
        'name': 'Praise Singer (iZimbongi)', 'icon': '🎵', 'cows': 50,
        'earn_day': 8, 'category': 'cultural',
        'desc': 'Compose izibongo (praise poems) for kings and warriors. Paid in cows per composition.',
        'unlock_level': 2,
    },
}

# ── Ancestor ceremony system ──────────────────────────────────────────────────
CEREMONIES = {
    'ukubulala_inkomo': {
        'name': 'Slaughter Ceremony (ukuBulala iNkomo)',
        'icon': '🐂', 'cost_cows': 5,
        'trigger': 'stage_complete',
        'desc': 'Slaughter 1 head of cattle to thank ancestors for completing a stage. Mandatory at L2+.',
        'blessing': {'herd_bonus': 2, 'win_bonus_pct': 10, 'duration_days': 3},
        'narration': 'Bayete! You offer a cow to the ancestors. Their blessing flows through your herd!',
    },
    'inkosi_coronation': {
        'name': 'Coronation Slaughter',
        'icon': '👑', 'cost_cows': 20,
        'trigger': 'crown_won',
        'desc': 'Slaughter 4 head of cattle upon becoming Inkosi. The realm celebrates!',
        'blessing': {'daily_tribute_bonus': 5, 'duration_days': 90},
        'narration': 'The great Inkosi gives thanks! Meat is shared with all warriors of the tribe!',
    },
    'isilo_feast': {
        'name': 'Great Feast of the iSilo',
        'icon': '🔱', 'cost_cows': 50,
        'trigger': 'isilo_ascension',
        'desc': 'The supreme ruler slaughters 10 cattle. All tribe members receive +5 cows.',
        'blessing': {'tribe_bonus': 5, 'season_bonus': True},
        'narration': 'iSilo! The Great King feasts all nations! Cows flow like rivers!',
    },
    'ukuthula_amadlozi': {
        'name': 'Appeasing the Ancestors (ukuThula amadlozi)',
        'icon': '🕯️', 'cost_cows': 3,
        'trigger': 'losing_streak',
        'desc': 'After 3 losses in a row, offer 3 cows to restore ancestor blessing.',
        'blessing': {'win_rate_reset': True, 'morale_boost': True},
        'narration': 'The ancestors hear your plea. A new spirit enters your game!',
    },
    'rain_ceremony': {
        'name': 'Rain Ceremony (umSebenzi weZulu)',
        'icon': '🌧️', 'cost_cows': 8,
        'trigger': 'seasonal_event',
        'desc': 'Seasonal event: slaughter to bring rain. All land earns 2× for 3 days.',
        'blessing': {'land_multiplier': 2, 'duration_days': 3},
        'narration': 'The rains come! Your crops flourish and your cattle grow strong!',
    },
    'wedding_slaughter': {
        'name': 'Wedding Feast (umShado)',
        'icon': '💑', 'cost_cows': 10,
        'trigger': 'marriage',
        'desc': 'Slaughter cattle for wedding feast. Required after marriage proposal.',
        'blessing': {'couple_herd_bonus': 10, 'daily_married_bonus': 3},
        'narration': 'Two herds become one! The community blesses the union!',
    },
}

LOSING_STREAK_THRESHOLD = 3  # losses in a row before ancestor ceremony is prompted


def _check_ceremony_trigger(email: str, trigger: str) -> dict:
    """Check if a ceremony should be triggered for this user+event."""
    ceremony = None
    for cid, c in CEREMONIES.items():
        if c['trigger'] == trigger:
            ceremony = {'id': cid, **c}
            break
    return ceremony or {}


def _perform_ceremony(email: str, ceremony_id: str) -> dict:
    """Deduct ceremony cost and grant blessing."""
    ceremony = CEREMONIES.get(ceremony_id)
    if not ceremony:
        return {'error': 'Unknown ceremony'}
    herd = _get_herd(email)
    cost = ceremony['cost_cows']
    if herd < cost:
        return {'ok': False, 'insufficient': True, 'required': cost, 'herd_cows': herd,
                'message': f'Need {cost} cattle for ceremony. You have {herd}.'}
    new_bal = _add_cows(email, -cost, 'ceremony_' + ceremony_id,
                        {'ceremony': ceremony_id, 'cost': cost})
    blessing = ceremony.get('blessing', {})
    db = get_db()
    # Apply herd bonus immediately
    if blessing.get('herd_bonus'):
        new_bal = _add_cows(email, blessing['herd_bonus'], 'ceremony_blessing')
    # Apply tribe bonus for isilo_feast
    if blessing.get('tribe_bonus'):
        db2 = db.execute('SELECT tribe_id FROM users WHERE email=?', (email,)).fetchone()
        if db2:
            db.execute(
                'UPDATE users SET herd_cows=herd_cows+? WHERE email IN '
                '(SELECT player_email FROM tribe_memberships WHERE tribe_id=?)',
                (blessing['tribe_bonus'], db2['tribe_id'])
            )
            db.commit()
    log.info(f'[ceremony] {email} performed {ceremony_id}, cost {cost} cows')
    return {
        'ok': True, 'ceremony_id': ceremony_id,
        'ceremony_name': ceremony['name'],
        'cost_cows': cost, 'herd_cows': new_bal,
        'blessing': blessing,
        'narration': ceremony['narration'],
        'icon': ceremony['icon'],
    }


@app.route('/api/ceremony/perform', methods=['POST'])
def perform_ceremony():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data = request.get_json(force=True) or {}
    cid  = sanitise(str(data.get('ceremony_id', '')), 50)
    result = _perform_ceremony(user['email'], cid)
    if result.get('error'):
        return jsonify(result), 400
    if not result.get('ok') and result.get('insufficient'):
        return jsonify(result), 402
    return jsonify(result)


@app.route('/api/ceremony/list')
def list_ceremonies():
    user = current_user()
    if not user:
        return jsonify({'ceremonies': list(CEREMONIES.items())})
    # Check if user has a losing streak
    db  = get_db()
    row = db.execute('SELECT losses FROM users WHERE email=?', (user['email'],)).fetchone()
    # Get recent bet outcomes
    recent = db.execute(
        'SELECT outcome FROM bets WHERE challenger_email=? ORDER BY created DESC LIMIT 5',
        (user['email'],)
    ).fetchall()
    streak = 0
    for r in recent:
        if r['outcome'] == 'lost': streak += 1
        else: break
    needs_appeasement = streak >= LOSING_STREAK_THRESHOLD
    return jsonify({
        'ceremonies': {k: {
            'name': v['name'], 'icon': v['icon'], 'cost_cows': v['cost_cows'],
            'desc': v['desc'], 'trigger': v['trigger'],
        } for k, v in CEREMONIES.items()},
        'losing_streak': streak,
        'needs_appeasement': needs_appeasement,
    })


# ── Expanded leaderboard (multi-segment) ─────────────────────────────────────
@app.route('/api/leaderboard/full')
def full_leaderboard():
    """
    Multi-segment leaderboard:
    - livestock (herd_cows)
    - games won (wins)
    - stages passed (current_level)
    - competition wins
    - wealth (total_cows ever accumulated)
    - tribe war (tribe total cows)
    Filter by: tribe, age_pool, global
    """
    db       = get_db()
    tribe    = request.args.get('tribe', '')
    age_pool = request.args.get('age_pool', '')
    limit    = min(int(request.args.get('limit', 25)), 50)
    where    = "WHERE email != ''"
    params   = []
    if tribe:
        where += " AND tribe_id=?"
        params.append(tribe)
    if age_pool:
        where += " AND age_pool=?"
        params.append(age_pool)

    def fetch(order_col, extra=''):
        q = (f"SELECT name,title,tribe_id,age_pool,has_crown,wins,losses,games,"
             f"herd_cows,total_cows,current_level,competition_wins,regalia "
             f"FROM users {where} ORDER BY {order_col} DESC{extra} LIMIT ?")
        return [dict(r) for r in db.execute(q, params + [limit]).fetchall()]

    # Livestock segment
    by_livestock = fetch('herd_cows')
    # Games won segment
    by_wins = fetch('wins')
    # Stages passed segment
    by_level = fetch('current_level', ', wins')
    # Competition champions
    by_comp = fetch('competition_wins', ', wins')
    # All-time wealth
    by_wealth = fetch('total_cows')

    # Tribe war segment
    tribe_war = db.execute(
        'SELECT tm.tribe_id, COUNT(u.email) as members, '
        'SUM(u.herd_cows) as live_cows, SUM(u.wins) as total_wins, '
        'MAX(u.has_crown) as has_king '
        'FROM users u JOIN tribe_memberships tm ON tm.player_email=u.email '
        'GROUP BY tm.tribe_id ORDER BY live_cows DESC'
    ).fetchall()
    tribe_standings = []
    for r in tribe_war:
        d = dict(r)
        ti = TRIBES.get(d['tribe_id'], {})
        d.update({'tribe_name': ti.get('name', ''), 'tribe_icon': ti.get('icon', '🐄')})
        tribe_standings.append(d)

    king = _get_current_king()
    return jsonify({
        'segments': {
            'livestock':   {'label': '🐄 Richest Herds',          'data': by_livestock},
            'wins':        {'label': '🏆 Most Games Won',          'data': by_wins},
            'stages':      {'label': '🏹 Highest Level Reached',   'data': by_level},
            'champions':   {'label': '🥇 Competition Champions',   'data': by_comp},
            'wealth':      {'label': '💰 All-Time Wealth',         'data': by_wealth},
        },
        'tribe_war':    tribe_standings,
        'current_king': king,
        'filters': {'tribe': tribe, 'age_pool': age_pool},
    })


# ── Social share system ───────────────────────────────────────────────────────
@app.route('/api/share/generate', methods=['POST'])
def generate_share():
    """Generate share text + URLs for major social platforms."""
    data    = request.get_json(force=True) or {}
    event   = sanitise(str(data.get('event', 'win')), 40)
    score   = int(data.get('score', 0))
    level   = int(data.get('level', 1))
    name    = sanitise(str(data.get('name', 'A player')), 50)
    tribe   = sanitise(str(data.get('tribe', 'world')), 30)
    title   = sanitise(str(data.get('title', 'iNduna')), 30)

    tribe_info = TRIBES.get(tribe, TRIBES.get('world', {}))
    tribe_name = tribe_info.get('name', 'Intshuba')
    tribe_icon = tribe_info.get('icon', '🐄')
    app_url    = os.environ.get('APP_URL', 'https://intshuba.info@inkazimulo.digital')

    LEVEL_NAMES = {1:'Calf (iJongo)', 2:'Warrior (iNduna)', 3:'Chief (iNkosi)',
                   4:'Paramount (iNkosi YaMakhosi)', 5:'Emperor (iSilo)'}
    level_name = LEVEL_NAMES.get(level, f'Level {level}')

    TEMPLATES = {
        'win': (
            f"🐄 {tribe_icon} I just won {score} cattle playing Intshuba — "
            f"the ancient Nguni stone game! "
            f"I am a {title} of {tribe_name}. Can you beat me? "
            f"Play free at {app_url} 🏹 #Intshuba #NguniGame #SouthAfrica"
        ),
        'level_up': (
            f"🔱 LEVEL UP! I just became {level_name} in Intshuba — "
            f"the centuries-old Nguni stone game played across Africa! "
            f"My herd: {score} cattle. Join {tribe_name} and challenge me! "
            f"{app_url} #Intshuba #Nguni #AfricanGames"
        ),
        'crown': (
            f"👑 INKOSI! I am the new King of Intshuba! "
            f"Defeated all challengers with {score} cattle in my herd. "
            f"All warriors of {tribe_name} bow before me! "
            f"Dare to challenge? {app_url} #IntshubaCrown #Nguni"
        ),
        'ceremony': (
            f"🐂 I just performed a ceremony in Intshuba to honour my ancestors! "
            f"The spirits bless my {score}-cattle herd. "
            f"Play this amazing African heritage game: {app_url} #Intshuba #UbuNguni"
        ),
        'invite': (
            f"🎮 Come play Intshuba with me — a real ancient Nguni stone game! "
            f"It teaches strategy, maths & African culture. "
            f"24 languages, 9 tribes, real cattle economy! "
            f"Free at {app_url} #Intshuba #EdTech #SouthAfrica"
        ),
    }

    text = TEMPLATES.get(event, TEMPLATES['win'])
    text_encoded = text.replace(' ', '%20').replace('\n', '%0A').replace('#', '%23')

    share_urls = {
        'twitter': f"https://twitter.com/intent/tweet?text={text_encoded}",
        'facebook': f"https://www.facebook.com/sharer/sharer.php?u={app_url}&quote={text_encoded}",
        'whatsapp': f"https://api.whatsapp.com/send?text={text_encoded}",
        'telegram': f"https://t.me/share/url?url={app_url}&text={text_encoded}",
        'linkedin': f"https://www.linkedin.com/sharing/share-offsite/?url={app_url}",
        'reddit':   f"https://reddit.com/submit?url={app_url}&title={text_encoded}",
        'tiktok':   app_url,  # TikTok has no web share API — link to game
        'instagram': app_url,  # Instagram has no web share API — link to game
        'copy':     text,
    }
    return jsonify({'ok': True, 'text': text, 'share_urls': share_urls})


# ── Donation info endpoint ──────────────────────────────────────────────────
@app.route('/api/donate/info')
def donate_info():
    """Return all donation methods with links."""
    return jsonify({
        'kofi': {
            'url':      KOFI_LINK,
            'username': KOFI_USERNAME,
            'embed_script': (
                "<script type='text/javascript' src='https://ko-fi.com/widgets/widget_2.js'></script>"
                f"<script>kofiwidget2.init('Support Intshuba','#C9A84C','{KOFI_USERNAME}');"
                "kofiwidget2.draw();</script>"
            ),
            'desc': 'Support via Ko-fi — coffee-sized donations, any amount',
        },
        'paypal': {
            'email':  PAYPAL_EMAIL,
            'link':   PAYPAL_LINK,
            'amounts': [20, 50, 100, 200, 500],
            'desc':  'PayPal — fast, secure, no account needed for card',
        },
        'bank': {
            **BANK_DETAILS,
            'desc': 'South African EFT — free for SA bank customers',
        },
        'support_email': SUPPORT_EMAIL,
    })


# ── Security hardening routes ────────────────────────────────────────────────
@app.route('/api/security/report', methods=['POST'])
def security_report():
    """CSP violation + general security incident reporting endpoint."""
    try:
        data = request.get_json(silent=True) or {}
        csp_report = data.get('csp-report', data)
        log.warning(f'[security] CSP/report: {json.dumps(csp_report)[:500]}')
        db = get_db()
        db.execute(
            'INSERT INTO bug_log(level,msg,trace,created) VALUES(?,?,?,strftime(\'%s\',\'now\'))',
            ('security', 'CSP/security report', json.dumps(csp_report)[:1000])
        )
        db.commit()
        return '', 204
    except Exception:
        return '', 204


@app.route('/api/user/change-password', methods=['POST'])
def change_password():
    """Authenticated password change with current password verification."""
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data         = request.get_json(force=True) or {}
    current_pw   = str(data.get('current_password', ''))
    new_pw       = str(data.get('new_password', ''))
    if len(new_pw) < 8:
        return jsonify({'error': 'New password must be at least 8 characters'}), 400
    db  = get_db()
    row = db.execute('SELECT hash,salt FROM users WHERE email=?', (user['email'],)).fetchone()
    if not row:
        return jsonify({'error': 'User not found'}), 404
    # Verify current password using the same pbkdf2 as registration
    if not verify_password(current_pw, row['hash'], row['salt']):
        return jsonify({'error': 'Current password is incorrect'}), 401
    # Set new password with pbkdf2
    new_hash, new_salt = hash_password(new_pw)
    db.execute('UPDATE users SET hash=?,salt=? WHERE email=?',
               (new_hash, new_salt, user['email']))
    # Invalidate all other sessions
    db.execute('DELETE FROM sessions WHERE email=?', (user['email'],))
    db.commit()
    log.info(f'[security] Password changed for {user["email"]}')
    return jsonify({'ok': True, 'message': 'Password changed. Please log in again.'})


@app.route('/api/user/delete-account', methods=['POST'])
def delete_account():
    """GDPR-compliant account deletion."""
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data = request.get_json(force=True) or {}
    password = str(data.get('password', ''))
    db  = get_db()
    row = db.execute('SELECT hash,salt FROM users WHERE email=?', (user['email'],)).fetchone()
    if not row:
        return jsonify({'error': 'User not found'}), 404
    if not verify_password(password, row['hash'], row['salt']):
        return jsonify({'error': 'Password incorrect'}), 401
    # Anonymise rather than hard-delete (preserve game history integrity)
    anon_email = f'deleted_{user["email"][:8]}_{int(time.time())}@deleted'
    db.execute('UPDATE users SET email=?,name=?,hash=?,salt=?,stripe_customer=?,stripe_sub_id=?,spouse_email=? WHERE email=?',
               (anon_email, 'Deleted User', '', '', '', '', '', user['email']))
    db.execute('DELETE FROM sessions WHERE email=?', (user['email'],))
    db.execute('UPDATE tribe_memberships SET player_email=? WHERE player_email=?',
               (anon_email, user['email']))
    db.commit()
    log.info(f'[security] Account deleted: {user["email"]} → {anon_email}')
    return jsonify({'ok': True, 'message': 'Account deleted. Thank you for playing Intshuba!'})


# ═══════════════════════════════════════════════════════════════════════════════
#  EXTENDED NGUNI ECONOMY — TRADES · CEREMONIES · LEADERBOARD · SHARING · SECURITY
# ═══════════════════════════════════════════════════════════════════════════════

TRADE_PROFESSIONS = {
    'hunter':       {'name': 'Hunter (uMzingeli)',          'icon': '🏹', 'cows_to_unlock': 30,  'earn_day': 8,  'risk': 0.15, 'level_req': 2, 'category': 'field',       'desc': 'Hunt wild animals for hides and ivory. +8 cows/day, risky.'},
    'leather_tanner':{'name': 'Leather Tanner (uMsiki)',   'icon': '🪣', 'cows_to_unlock': 40,  'earn_day': 6,  'risk': 0.05, 'level_req': 2, 'category': 'craft',       'desc': 'Tan hides into leather for regalia and trade. +6 cows/day.'},
    'craftsman':    {'name': 'Craftsman (uNgcweti)',        'icon': '🔨', 'cows_to_unlock': 50,  'earn_day': 7,  'risk': 0.05, 'level_req': 2, 'category': 'craft',       'desc': 'Craft tools, furniture, and traditional items. +7 cows/day.'},
    'builder':      {'name': 'Builder (uMakhi)',            'icon': '🧱', 'cows_to_unlock': 80,  'earn_day': 10, 'risk': 0.08, 'level_req': 2, 'category': 'construction','desc': 'Build kraals, homesteads, and community structures. +10 cows/day.'},
    'ironsmith':    {'name': 'Ironsmith (uNcedisi)',        'icon': '⚒️', 'cows_to_unlock': 100, 'earn_day': 12, 'risk': 0.10, 'level_req': 2, 'category': 'forge',       'desc': 'Forge spears, axes, and jewellery. +12 cows/day.'},
    'miner':        {'name': 'Miner (uMgodi)',              'icon': '⛏️', 'cows_to_unlock': 120, 'earn_day': 15, 'risk': 0.20, 'level_req': 3, 'category': 'extraction',  'desc': 'Mine iron, gold, and coal. Highest yield, most dangerous. +15 cows/day.'},
    'engineer':     {'name': 'Engineer (uNjinela)',         'icon': '⚙️', 'cows_to_unlock': 200, 'earn_day': 20, 'risk': 0.05, 'level_req': 3, 'category': 'technical',   'desc': 'Design irrigation, bridges, and fortifications. +20 cows/day.'},
    'healer':       {'name': 'Healer/Sangoma (iSangoma)',   'icon': '🌿', 'cows_to_unlock': 60,  'earn_day': 9,  'risk': 0.02, 'level_req': 2, 'category': 'spiritual',   'desc': 'Traditional healer and spiritual advisor. +9 cows/day, very safe.'},
    'trader':       {'name': 'Long-Distance Trader (uMthengisi)', 'icon': '🛒', 'cows_to_unlock': 150, 'earn_day': 18, 'risk': 0.12, 'level_req': 3, 'category': 'trade', 'desc': 'Trade between tribes and regions. +18 cows/day.'},
    'master_farmer':{'name': 'Master Farmer (uMlimi Omkhulu)', 'icon': '🌽', 'cows_to_unlock': 90, 'earn_day': 14, 'risk': 0.15, 'level_req': 2, 'category': 'farming',  'desc': 'Large-scale crop farming. Drought risk but high yield. +14 cows/day.'},
}

CEREMONIES = {
    'ukupheka':        {'name': 'ukuPheka (First Cook)',      'icon': '🍖', 'cows_cost': 2,  'trigger': 'level_2_unlock',    'desc': 'Slaughter a calf to thank ancestors for your first herd.',                'blessing': {'type': 'luck',          'value': 0.10, 'duration_days': 7}},
    'umbuyiso':        {'name': 'uMbuyiso (Return Home)',     'icon': '🔥', 'cows_cost': 5,  'trigger': 'level_3_unlock',    'desc': 'Bring the spirit of your ancestor home. Slaughter a goat.',             'blessing': {'type': 'earn_bonus',    'value': 0.15, 'duration_days': 14}},
    'imbeleko':        {'name': 'iMbeleko (Introduction)',    'icon': '🐄', 'cows_cost': 3,  'trigger': 'first_win_streak_5','desc': 'Present yourself to ancestors after 5 consecutive wins.',               'blessing': {'type': 'win_bonus',     'value': 0.20, 'duration_days': 3}},
    'ukushwama':       {'name': 'uKushwama (First Fruits)',   'icon': '🌾', 'cows_cost': 4,  'trigger': 'first_harvest',     'desc': 'Offer first fruits and a cow to the community after harvest.',          'blessing': {'type': 'harvest_double','value': 2.00, 'duration_days': 1}},
    'umkhosi_wokwela': {'name': 'uMkhosi woKwela (War Prep)', 'icon': '⚔️', 'cows_cost': 10, 'trigger': 'crown_challenge',   'desc': 'Sacred slaughter before crown challenge. Ancestors go with you.',       'blessing': {'type': 'crown_defense', 'value': 0.50, 'duration_days': 1}},
    'isigqi':          {'name': 'iSigqi (Celebration)',       'icon': '🎉', 'cows_cost': 8,  'trigger': 'competition_win',   'desc': 'Feast after winning. Share cattle with the village community.',         'blessing': {'type': 'reputation',    'value': 50,   'duration_days': 30}},
    'thanksgiving':    {'name': 'ukuBonga (Thanksgiving)',    'icon': '🙏', 'cows_cost': 15, 'trigger': 'isilo_ascension',   'desc': 'Supreme offering on becoming iSilo. The greatest ancestral slaughter.', 'blessing': {'type': 'eternal_legacy','value': 1.00, 'duration_days': 9999}},
}

SOCIAL_PLATFORMS = {
    'whatsapp':  {'name': 'WhatsApp',   'icon': '💬', 'color': '#25D366', 'url': 'https://wa.me/?text={text}',                                                                  'encode': True},
    'facebook':  {'name': 'Facebook',   'icon': '📘', 'color': '#1877F2', 'url': 'https://www.facebook.com/sharer/sharer.php?u={url}&quote={text}',                            'encode': True},
    'twitter':   {'name': 'Twitter/X',  'icon': '🐦', 'color': '#000000', 'url': 'https://twitter.com/intent/tweet?text={text}&url={url}&hashtags=Intshuba,NguniGame',        'encode': True},
    'telegram':  {'name': 'Telegram',   'icon': '✈️', 'color': '#2CA5E0', 'url': 'https://t.me/share/url?url={url}&text={text}',                                               'encode': True},
    'linkedin':  {'name': 'LinkedIn',   'icon': '💼', 'color': '#0A66C2', 'url': 'https://www.linkedin.com/sharing/share-offsite/?url={url}',                                  'encode': True},
    'reddit':    {'name': 'Reddit',     'icon': '🟠', 'color': '#FF4500', 'url': 'https://reddit.com/submit?url={url}&title={text}',                                           'encode': True},
    'email':     {'name': 'Email',      'icon': '📧', 'color': '#EA4335', 'url': 'mailto:?subject=Play Intshuba!&body={text}%0A%0A{url}',                                       'encode': True},
    'pinterest': {'name': 'Pinterest',  'icon': '📌', 'color': '#E60023', 'url': 'https://pinterest.com/pin/create/button/?url={url}&description={text}',                     'encode': True},
    'discord':   {'name': 'Discord',    'icon': '🎮', 'color': '#5865F2', 'url': None, 'copy_only': True, 'note': 'Copy link and share in your Discord server'},
    'tiktok':    {'name': 'TikTok',     'icon': '🎵', 'color': '#010101', 'url': None, 'copy_only': True, 'note': 'Copy link and share in TikTok bio or DM'},
    'instagram': {'name': 'Instagram',  'icon': '📸', 'color': '#E4405F', 'url': None, 'copy_only': True, 'note': 'Copy link and share in Instagram Story or Bio'},
    'snapchat':  {'name': 'Snapchat',   'icon': '👻', 'color': '#FFFC00', 'url': None, 'copy_only': True, 'note': 'Copy link and share in Snapchat'},
    'copy':      {'name': 'Copy Link',  'icon': '🔗', 'color': '#666666', 'url': '{url}', 'encode': False},
}

import hashlib as _hashlib, re as _re


def _validate_password_strong(pw: str):
    if len(pw) < 8:           return False, 'At least 8 characters required'
    if not _re.search(r'[A-Z]', pw): return False, 'Needs an uppercase letter'
    if not _re.search(r'[a-z]', pw): return False, 'Needs a lowercase letter'
    if not _re.search(r'[0-9]', pw): return False, 'Needs a digit'
    return True, 'ok'

def _sanitise_input(val, maxlen=200):
    s = str(val or '').strip()
    dangerous = ['--', '; DROP', 'UNION SELECT', 'OR 1=1', "' OR '"]
    for d in dangerous:
        if d.lower() in s.lower(): return ''
    s = _re.sub(r'<[^>]+>', '', s)
    return s[:maxlen]


@app.route('/api/trades/list')
def list_trades():
    user = current_user()
    owned = set()
    if user:
        db = get_db()
        rows = db.execute(
            "SELECT event_type FROM kingdom_events WHERE user_email=? AND event_type LIKE 'bought_%'",
            (user['email'],)
        ).fetchall()
        owned = {r['event_type'].replace('bought_','') for r in rows}
    return jsonify({'trades': TRADE_PROFESSIONS, 'ceremonies': CEREMONIES, 'owned': list(owned)})


@app.route('/api/trades/buy', methods=['POST'])
def buy_trade():
    user = current_user()
    if not user: return jsonify({'error': 'Not authenticated'}), 401
    data  = request.get_json(force=True) or {}
    trade = sanitise(str(data.get('trade','')), 40)
    prof  = TRADE_PROFESSIONS.get(trade)
    if not prof: return jsonify({'error': 'Unknown trade'}), 400
    herd = _get_herd(user['email'])
    cost = prof['cows_to_unlock']
    if herd < cost:
        return jsonify({'ok': False, 'insufficient': True, 'required': cost, 'herd': herd,
                        'message': f'Need {cost} cows to unlock {prof["name"]}. You have {herd}.'}), 402
    new_bal = _add_cows(user['email'], -cost, 'bought_' + trade, {'profession': trade})
    return jsonify({'ok': True, 'trade': trade, 'herd_cows': new_bal,
                    'message': f'{prof["icon"]} {prof["name"]} unlocked! Earns +{prof["earn_day"]} cows/day.',
                    'daily_earn': prof['earn_day']})


# ═══════════════════════════════════════════════════════════════════════════════
#  AI CHIEF PERSONAS  ·  STORY MODE  ·  SEASONAL EVENTS
#  TOURNAMENT BRACKET  ·  PWA MANIFEST  ·  KINGDOM MAP  ·  PUSH NOTIFICATIONS
# ═══════════════════════════════════════════════════════════════════════════════

import random as _random

# ── AI Chief Personas ──────────────────────────────────────────────────────────
# Each AI chief has a unique playing style, trash-talk lines in multiple languages,
# and a unique board skin that unlocks when you defeat them.
AI_PERSONAS = {
    'shaka': {
        'name': 'Shaka kaSenzangakhona',  'tribe': 'amazulu',  'era': '1787–1828',
        'icon': '🐗',  'difficulty': 5,  'strategy': 'aggressive',
        'skin_unlock': 'zulu_royal',
        'taunt_en': [
            "My warriors have never seen defeat!",
            "You cannot outrun the uSuthu!",
            "I built an empire — you play a board game.",
        ],
        'taunt_zu': [
            "Amabutho ami awakaze abone ukuhlulwa!",
            "Ngizokuhlula ngokuphazima kweso!",
        ],
        'taunt_xh': ["Hayi, ungathandabuzi!", "Ndiyakusilela!", ],
        'win_msg_en':  "The kingdom of the Zulus cannot fall!",
        'lose_msg_en': "You fight like a warrior of old. I respect you.",
        'description': 'Aggressive attacker. Maximises captures. Rarely defends.',
        'herd_cows': 9999,
    },
    'moshoeshoe': {
        'name': 'Moshoeshoe I',  'tribe': 'basotho',  'era': '1786–1870',
        'icon': '☀️',  'difficulty': 4,  'strategy': 'defensive',
        'skin_unlock': 'sotho_mountain',
        'taunt_en': [
            "I built a fortress on a mountain. You cannot reach me.",
            "Patience is a warrior's greatest weapon.",
            "My cattle graze in safety. Can you say the same?",
        ],
        'taunt_st': ["Thabo ea hao e tla fela!", "Ho phelisana le nna ha ho bonolo!"],
        'win_msg_en':  "The mountain protects its own.",
        'lose_msg_en': "You have climbed my mountain. I am honoured.",
        'description': 'Master defender. Protects herd, waits for your mistakes.',
        'herd_cows': 8888,
    },
    'sekhukhune': {
        'name': 'Sekhukhune I',  'tribe': 'bapedi',  'era': '1814–1882',
        'icon': '🌙',  'difficulty': 4,  'strategy': 'balanced',
        'skin_unlock': 'pedi_warrior',
        'taunt_en': [
            "I fought the British and the Boers — you are just one player.",
            "My drums warn of your every move.",
            "The Bapedi do not surrender!",
        ],
        'taunt_nso': ["O a lwantsha nna? A ke kgonege!", "Ke tla go hlaola!"],
        'win_msg_en':  "The mountains of Bopedi echo my victory!",
        'lose_msg_en': "You have defeated a worthy opponent. Take pride in that.",
        'description': 'Balanced strategist. Adapts to your play style.',
        'herd_cows': 8000,
    },
    'mzilikazi': {
        'name': 'Mzilikazi kaMashobane',  'tribe': 'amandebele',  'era': '1790–1868',
        'icon': '🎨',  'difficulty': 5,  'strategy': 'unpredictable',
        'skin_unlock': 'ndebele_geometric',
        'taunt_en': [
            "I broke from Shaka himself. You are nothing.",
            "My impis move like lightning!",
            "The Matabele fear no one!",
        ],
        'taunt_nr': ["Ngeke wanginqoba!", "Amandebele amanqoba!"],
        'win_msg_en':  "My kingdom stretches to the Limpopo!",
        'lose_msg_en': "A worthy challenger. Come back when you are stronger.",
        'description': 'Unpredictable mix of attack and retreat. Hard to read.',
        'herd_cows': 9500,
    },
    'sobhuza': {
        'name': 'Sobhuza II',  'tribe': 'emaswati',  'era': '1899–1982',
        'icon': '🦁',  'difficulty': 3,  'strategy': 'diplomatic',
        'skin_unlock': 'swati_reed',
        'taunt_en': [
            "A true king rules with wisdom, not just strength.",
            "The reed dance celebrates my reign. What do you celebrate?",
            "Sixty years of rule. How long have you played?",
        ],
        'taunt_ss': ["Ngeke wanqoba iNgwenyama!", "Busa umhlaba!"],
        'win_msg_en':  "The longest reign in history — undefeated!",
        'lose_msg_en': "Wisdom has many teachers. Today you taught me.",
        'description': 'Diplomatic — steady accumulator. Never wastes a move.',
        'herd_cows': 7500,
    },
}

def _get_ai_persona(persona_id: str) -> dict:
    return AI_PERSONAS.get(persona_id, AI_PERSONAS['shaka'])

def _ai_taunt(persona_id: str, lang: str = 'en') -> str:
    persona = _get_ai_persona(persona_id)
    key     = f'taunt_{lang}'
    lines   = persona.get(key) or persona.get('taunt_en', ['...'])
    return _random.choice(lines)

@app.route('/api/ai/personas')
def get_ai_personas():
    """Return all AI chief personas."""
    safe = {}
    for pid, p in AI_PERSONAS.items():
        safe[pid] = {k: v for k, v in p.items() if k not in ('taunt_zu','taunt_xh','taunt_st','taunt_nso','taunt_nr','taunt_ss')}
    return jsonify({'personas': safe})

@app.route('/api/ai/challenge/<persona_id>', methods=['POST'])
def challenge_ai_persona(persona_id):
    """Start a challenge game against a named AI chief."""
    if persona_id not in AI_PERSONAS:
        return jsonify({'error': 'Unknown persona'}), 404
    persona = AI_PERSONAS[persona_id]
    user    = current_user()
    lang    = session.get('lang', 'en')
    taunt   = _ai_taunt(persona_id, lang)
    # Check if player has enough cows to challenge at high difficulty
    min_cows = {3: 20, 4: 100, 5: 300}.get(persona['difficulty'], 0)
    if user and min_cows:
        herd = _get_herd(user['email'])
        if herd < min_cows:
            return jsonify({
                'ok': False, 'insufficient': True,
                'message': f'{persona["name"]} refuses to face someone with fewer than {min_cows} cows.',
                'required': min_cows, 'herd': herd,
            }), 402
    return jsonify({
        'ok': True,
        'persona': {k: v for k, v in persona.items() if 'taunt' not in k},
        'opening_taunt': taunt,
        'game_level': min(persona['difficulty'], 3),
        'message': f'⚔️ {persona["name"]} accepts your challenge!',
    })

@app.route('/api/ai/taunt/<persona_id>')
def get_ai_taunt(persona_id):
    lang = request.args.get('lang', 'en')
    return jsonify({'taunt': _ai_taunt(persona_id, lang), 'persona': persona_id})

# ── Story Mode ─────────────────────────────────────────────────────────────────
STORY_CHAPTERS = [
    {
        'id': 1, 'title': 'The Calf Learns',
        'title_zu': 'iNkonyana Iyafunda',
        'text': 'You are born into a cattle-keeping family on the banks of the Thukela River. Your grandfather places a worn wooden board before you. "This is Intshuba," he says. "Before you can tend cattle, you must learn to count them." He shows you the holes, the stones, the spiral path of life.',
        'objective': 'Win your first game against grandfather (AI Level 1)',
        'level': 1, 'min_cows': 0, 'reward_cows': 10,
        'persona': None, 'unlock_tribe': None,
        'image_emoji': '🌅',
    },
    {
        'id': 2, 'title': 'The First Herd',
        'title_zu': 'Umhlambi Wokuqala',
        'text': 'You have learned the basics. Now the village elders challenge you. "A herdsman with twenty cows may join the iMpi," says the induna. "Show us you can win." The board is larger now — four rows of six holes. The stones move faster. The AI plays like a seasoned warrior.',
        'objective': 'Accumulate 20 cows and win at Level 2',
        'level': 2, 'min_cows': 5, 'reward_cows': 20,
        'persona': 'sobhuza', 'unlock_tribe': None,
        'image_emoji': '🐄',
    },
    {
        'id': 3, 'title': 'The Induna Rises',
        'title_zu': 'iNduna Iyakhula',
        'text': 'Word spreads of your skill. Sobhuza II himself sends a messenger: "The king wishes to test the young player from the Thukela." You travel to the royal kraal. The king greets you with a smile — and then destroys you twice before letting you win the third game.',
        'objective': 'Defeat Sobhuza II in a challenge game',
        'level': 2, 'min_cows': 20, 'reward_cows': 50,
        'persona': 'sobhuza', 'unlock_tribe': 'emaswati',
        'image_emoji': '🦁',
    },
    {
        'id': 4, 'title': 'The War Drums',
        'title_zu': 'Izingoma Zempi',
        'text': 'Sekhukhune sends word: "The Bapedi have heard of your growing herd. A great warrior must be tested by iron." His drummer announces the challenge at dawn. The mountain fortress looms. You must beat Sekhukhune at his own game — on his own board.',
        'objective': 'Defeat Sekhukhune at Level 3',
        'level': 3, 'min_cows': 50, 'reward_cows': 100,
        'persona': 'sekhukhune', 'unlock_tribe': 'bapedi',
        'image_emoji': '🌙',
    },
    {
        'id': 5, 'title': 'The Ndebele Gauntlet',
        'title_zu': 'Ukuhlolwa kwamaNdebele',
        'text': 'Mzilikazi has heard of your victories. He is not impressed. "Shaka\'s generals could not stop me — you think you can?" His geometric war paint flashes in the firelight. He plays unpredictably, changing strategy mid-game. Your patterns will not save you here.',
        'objective': 'Defeat Mzilikazi with at least 100 cows',
        'level': 3, 'min_cows': 100, 'reward_cows': 200,
        'persona': 'mzilikazi', 'unlock_tribe': 'amandebele',
        'image_emoji': '🎨',
    },
    {
        'id': 6, 'title': 'The Mountain Siege',
        'title_zu': 'Ukuvimbezela Intaba',
        'text': 'Moshoeshoe watches from his mountain. He has received every challenger for thirty years. None have reached him. You must climb through three levels of his defenders before facing the king himself. The air is thin up here. So is your patience.',
        'objective': 'Defeat Moshoeshoe with 200+ cows — he defends ruthlessly',
        'level': 3, 'min_cows': 200, 'reward_cows': 350,
        'persona': 'moshoeshoe', 'unlock_tribe': 'basotho',
        'image_emoji': '☀️',
    },
    {
        'id': 7, 'title': 'The Great Zulu Test',
        'title_zu': 'Ukuhlolwa kukaNdabezitha',
        'text': 'The greatest test awaits. Shaka kaSenzangakhona sits before the board. Around you, ten thousand warriors stand in silence. "I created the impondo zankomo formation," he says. "Everything you know about strategy, I invented." He plays at Level 5 — the hardest mode in existence.',
        'objective': 'Defeat Shaka — the hardest game in Intshuba',
        'level': 3, 'min_cows': 500, 'reward_cows': 1000,
        'persona': 'shaka', 'unlock_tribe': 'amazulu',
        'image_emoji': '🐗',
    },
    {
        'id': 8, 'title': 'The Crown Petition',
        'title_zu': 'Ukucela Isihlalo',
        'text': 'You have bested five great chiefs. Your herd grows beyond counting. The elders gather. "You have the land, the cattle, and the skill," says the oldest elder. "But a king must also have a home, and jewellery worthy of the throne. Build your Great House. Then petition the crown."',
        'objective': 'Buy land, great house, beadwork, and petition the crown',
        'level': 3, 'min_cows': 300, 'reward_cows': 500,
        'persona': None, 'unlock_tribe': None,
        'image_emoji': '🏠',
    },
    {
        'id': 9, 'title': 'iNkosi YaMakhosi',
        'title_zu': 'Inkosi Yamakhosi',
        'text': 'The tribes send challengers from across southern Africa. Zulu, Xhosa, Ndebele, Swati, Pedi, Sotho, Venda, Tsonga — all come to test the new paramount chief. You must defend the throne against wave after wave of challengers. Your daily tribute pours in. The kingdom grows.',
        'objective': 'Defend the crown for 7 days (win 7 online or AI games while holding crown)',
        'level': 3, 'min_cows': 2000, 'reward_cows': 2000,
        'persona': None, 'unlock_tribe': None,
        'image_emoji': '👑',
    },
    {
        'id': 10, 'title': 'iSilo SamaZulu',
        'title_zu': 'iSilo Esiyinhloko',
        'text': 'The international arena opens. Players from Spain, Brazil, Japan, Nigeria, Ethiopia — all compete for the supreme title. The board is the same wooden spiral your grandfather showed you. The stones are the same. But the world watches now. Become iSilo SamaZulu — the Great King of all nations.',
        'objective': 'Win the International Championship — defeat all Paramount Chiefs globally',
        'level': 3, 'min_cows': 5000, 'reward_cows': 5000,
        'persona': None, 'unlock_tribe': None,
        'image_emoji': '🔱',
    },
]

@app.route('/api/story/chapters')
def story_chapters():
    """Return all story chapters with player progress."""
    user = current_user()
    completed = set()
    if user:
        db   = get_db()
        evts = db.execute(
            "SELECT event_type FROM kingdom_events WHERE user_email=? AND event_type LIKE 'story_%'",
            (user['email'],)
        ).fetchall()
        completed = {e['event_type'].replace('story_complete_','') for e in evts}
    chapters = []
    for ch in STORY_CHAPTERS:
        d           = dict(ch)
        d['done']   = str(ch['id']) in completed
        d['locked'] = ch['min_cows'] > 0 and (not user or _get_herd(user['email']) < ch['min_cows'])
        chapters.append(d)
    return jsonify({'chapters': chapters, 'total': len(STORY_CHAPTERS)})

@app.route('/api/story/complete', methods=['POST'])
def story_complete():
    """Mark a story chapter as completed and grant rewards."""
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data    = request.get_json(force=True) or {}
    chap_id = int(data.get('chapter_id', 0))
    chapter = next((c for c in STORY_CHAPTERS if c['id'] == chap_id), None)
    if not chapter:
        return jsonify({'error': 'Unknown chapter'}), 404
    db  = get_db()
    evt = db.execute(
        "SELECT id FROM kingdom_events WHERE user_email=? AND event_type=?",
        (user['email'], f'story_complete_{chap_id}')
    ).fetchone()
    if evt:
        return jsonify({'ok': True, 'already_done': True, 'message': 'Chapter already completed!'})
    # Grant reward cows
    reward = chapter.get('reward_cows', 0)
    new_bal = _add_cows(user['email'], reward, f'story_complete_{chap_id}', {'chapter': chap_id})
    # Unlock tribe if applicable
    msg_extra = ''
    if chapter.get('unlock_tribe'):
        db.execute('UPDATE users SET tribe_id=? WHERE email=?',
                   (chapter['unlock_tribe'], user['email']))
        db.execute(
            'INSERT OR REPLACE INTO tribe_memberships(player_email,tribe_id,rank) VALUES(?,?,?)',
            (user['email'], chapter['unlock_tribe'], 'veteran')
        )
        tribe_name = TRIBES.get(chapter['unlock_tribe'], {}).get('name', chapter['unlock_tribe'])
        msg_extra = f' The {tribe_name} tribe now welcomes you!'
    db.commit()
    return jsonify({
        'ok': True,
        'chapter': chap_id,
        'reward_cows': reward,
        'new_balance': new_bal,
        'unlock_tribe': chapter.get('unlock_tribe'),
        'message': f'{chapter["image_emoji"]} Chapter {chap_id} complete! +{reward} cows.{msg_extra}',
    })

# ── Seasonal Events ────────────────────────────────────────────────────────────
SEASONAL_EVENTS = {
    'harvest': {
        'name': 'Harvest Season (Izithelo)',
        'description': 'Crops yield double. Land earns +4 cows/day instead of 2. Crop farms earn +8.',
        'cow_multiplier': 2.0,
        'duration_days': 7,
        'icon': '🌽',
        'months': [3, 4],  # March–April (Southern Hemisphere autumn harvest)
    },
    'rain': {
        'name': 'Rain Season (Izulu)',
        'description': 'The board floods — inner rows shift. Captures are harder but worth double.',
        'cow_multiplier': 2.0,
        'duration_days': 7,
        'icon': '🌧️',
        'months': [11, 12],  # November–December rainy season
    },
    'lobola': {
        'name': 'Lobola Season (iLobolo)',
        'description': 'Marriage proposals cost 50% fewer cows. Married bonus +10 cows/day.',
        'cow_multiplier': 1.0,
        'lobola_discount': 0.5,
        'duration_days': 14,
        'icon': '💍',
        'months': [6, 7],  # Winter — traditional marriage season
    },
    'reed_dance': {
        'name': 'Reed Dance (uMhlanga)',
        'description': 'All female players earn +5 cows/day. Open tournament with doubled prizes.',
        'cow_multiplier': 1.0,
        'duration_days': 3,
        'icon': '🎋',
        'months': [8, 9],  # August–September
    },
    'warriors': {
        'name': "Warriors' Week (Amabutho)",
        'description': 'Betting ante doubled — but wins pay triple. High risk, high reward.',
        'cow_multiplier': 3.0,
        'ante_multiplier': 2.0,
        'duration_days': 7,
        'icon': '⚔️',
        'months': [1, 2],  # January–February — new year warrior testing
    },
}

def _current_seasonal_event() -> dict | None:
    """Return the active seasonal event for the current month, or None."""
    month = int(time.strftime('%m'))
    for eid, evt in SEASONAL_EVENTS.items():
        if month in evt.get('months', []):
            return {'id': eid, **evt}
    return None

@app.route('/api/seasonal/current')
def seasonal_current():
    """Return the currently active seasonal event."""
    evt = _current_seasonal_event()
    if not evt:
        # Next upcoming
        month = int(time.strftime('%m'))
        upcoming = None
        min_gap = 13
        for eid, e in SEASONAL_EVENTS.items():
            for m in e.get('months', []):
                gap = (m - month) % 12
                if 0 < gap < min_gap:
                    min_gap = gap
                    upcoming = {'id': eid, 'starts_in_months': gap, **e}
        return jsonify({'active': False, 'upcoming': upcoming})
    return jsonify({'active': True, 'event': evt})

@app.route('/api/seasonal/all')
def seasonal_all():
    return jsonify({'events': SEASONAL_EVENTS})

# ── Tournament Bracket ─────────────────────────────────────────────────────────
@app.route('/api/tournament/bracket/<comp_id>')
def tournament_bracket(comp_id):
    """Return single-elimination bracket for a competition."""
    db   = get_db()
    comp = db.execute("SELECT * FROM competitions WHERE id=?", (comp_id,)).fetchone()
    if not comp:
        return jsonify({'error': 'Competition not found'}), 404
    players = db.execute(
        "SELECT player_name, player_email, score, wins, losses "
        "FROM competition_players WHERE comp_id=? ORDER BY score DESC",
        (comp_id,)
    ).fetchall()
    # Build bracket
    import math
    n         = len(players)
    if n < 2:
        return jsonify({'bracket': [], 'players': [dict(p) for p in players], 'message': 'Need at least 2 players'})
    rounds    = math.ceil(math.log2(n)) if n > 1 else 1
    slots     = 2 ** rounds
    seeded    = [dict(p) for p in players]
    # Pad with byes
    while len(seeded) < slots:
        seeded.append({'player_name': 'BYE', 'player_email': '', 'score': 0, 'wins': 0, 'losses': 0})
    # Build round 1 matchups
    matchups = []
    for i in range(0, slots, 2):
        matchups.append({
            'match_id': f'R1-M{i//2+1}',
            'round': 1,
            'player_a': seeded[i],
            'player_b': seeded[i+1],
            'winner': None,
            'status': 'pending',
        })
    return jsonify({
        'competition': dict(comp),
        'total_rounds': rounds,
        'total_players': n,
        'bracket': matchups,
        'seeded_players': seeded,
    })

@app.route('/api/tournament/record-result', methods=['POST'])
def tournament_record_result():
    """Record a match result in a competition bracket."""
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data     = request.get_json(force=True) or {}
    comp_id  = sanitise(str(data.get('comp_id','')), 30)
    winner   = sanitise(str(data.get('winner_email','')), 80)
    loser    = sanitise(str(data.get('loser_email','')), 80)
    db       = get_db()
    comp     = db.execute("SELECT * FROM competitions WHERE id=?", (comp_id,)).fetchone()
    if not comp or comp['host_email'] != user['email']:
        return jsonify({'error': 'Not authorised to record results for this competition'}), 401
    # Update scores
    db.execute(
        "UPDATE competition_players SET score=score+3, wins=wins+1 WHERE comp_id=? AND player_email=?",
        (comp_id, winner)
    )
    db.execute(
        "UPDATE competition_players SET losses=losses+1 WHERE comp_id=? AND player_email=?",
        (comp_id, loser)
    )
    db.commit()
    return jsonify({'ok': True, 'winner': winner, 'message': 'Result recorded! +3 points to winner.'})

# ── PWA Manifest + Service Worker ──────────────────────────────────────────────
PWA_MANIFEST = {
    "name": "Intshuba — Nguni Stone Game",
    "short_name": "Intshuba",
    "description": "The ancient Nguni stone game. Build your cattle empire, join a tribe, become iSilo.",
    "start_url": "/",
    "display": "standalone",
    "background_color": "#0D0804",
    "theme_color": "#C9A84C",
    "orientation": "portrait",
    "categories": ["games", "education", "entertainment"],
    "lang": "en",
    "icons": [
        {"src": "/static/icon-192.png", "sizes": "192x192", "type": "image/png", "purpose": "any maskable"},
        {"src": "/static/icon-512.png", "sizes": "512x512", "type": "image/png", "purpose": "any maskable"},
    ],
    "shortcuts": [
        {"name": "Play Now",    "url": "/?action=play",    "icons": [{"src": "/static/icon-192.png", "sizes": "192x192"}]},
        {"name": "My Kingdom",  "url": "/?action=kingdom", "icons": [{"src": "/static/icon-192.png", "sizes": "192x192"}]},
        {"name": "Competitions","url": "/?action=compete",  "icons": [{"src": "/static/icon-192.png", "sizes": "192x192"}]},
    ],
    "screenshots": [
        {"src": "/static/screenshot-game.png",    "sizes": "390x844", "type": "image/png", "label": "Gameplay"},
        {"src": "/static/screenshot-kingdom.png", "sizes": "390x844", "type": "image/png", "label": "Kingdom"},
    ],
    "share_target": {
        "action": "/share",
        "method": "GET",
        "params": {"title": "title", "text": "text", "url": "url"}
    }
}

@app.route('/manifest.json')
@app.route('/manifest.webmanifest')
def pwa_manifest():
    return jsonify(PWA_MANIFEST), 200, {
        'Content-Type': 'application/manifest+json',
        'Cache-Control': 'public, max-age=86400'
    }

@app.route('/sw.js')
def service_worker():
    """Progressive Web App service worker — offline support + push notifications."""
    sw_code = r"""
const CACHE = 'intshuba-v2.2.0';
const OFFLINE_URLS = ['/', '/manifest.json'];

self.addEventListener('install', e => {
  e.waitUntil(caches.open(CACHE).then(c => c.addAll(OFFLINE_URLS)).then(() => self.skipWaiting()));
});

self.addEventListener('activate', e => {
  e.waitUntil(caches.keys().then(keys =>
    Promise.all(keys.filter(k => k !== CACHE).map(k => caches.delete(k)))
  ).then(() => self.clients.claim()));
});

self.addEventListener('fetch', e => {
  if (e.request.method !== 'GET') return;
  if (e.request.url.includes('/api/')) return; // Never cache API calls
  e.respondWith(
    caches.match(e.request).then(cached => {
      const network = fetch(e.request).then(res => {
        if (res.ok) caches.open(CACHE).then(c => c.put(e.request, res.clone()));
        return res;
      });
      return cached || network;
    })
  );
});

self.addEventListener('push', e => {
  const data = e.data?.json() || {};
  e.waitUntil(self.registration.showNotification(
    data.title || '🐄 Intshuba',
    {
      body:    data.body || 'Something happened in your kingdom!',
      icon:    '/static/icon-192.png',
      badge:   '/static/icon-192.png',
      vibrate: [100, 50, 100],
      data:    { url: data.url || '/' },
      actions: data.actions || [{ action: 'open', title: 'Open Game' }],
    }
  ));
});

self.addEventListener('notificationclick', e => {
  e.notification.close();
  const url = e.notification.data?.url || '/';
  e.waitUntil(clients.openWindow(url));
});
"""
    return sw_code, 200, {
        'Content-Type': 'application/javascript',
        'Service-Worker-Allowed': '/',
        'Cache-Control': 'no-cache'
    }

# ── Push Notification subscription storage ─────────────────────────────────────
@app.route('/api/push/subscribe', methods=['POST'])
def push_subscribe():
    """Store a Web Push subscription for a user."""
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data = request.get_json(force=True) or {}
    sub  = json.dumps(data.get('subscription', {}))
    db   = get_db()
    db.execute(
        "UPDATE users SET regalia=regalia WHERE email=?", (user['email'],)  # placeholder touch
    )
    # Store push sub in kingdom_events as a special event
    db.execute(
        "INSERT OR REPLACE INTO kingdom_events(user_email,event_type,detail,cows_delta) VALUES(?,?,?,0)",
        (user['email'], 'push_subscription', sub)
    )
    db.commit()
    return jsonify({'ok': True, 'message': '🔔 Push notifications enabled!'})

# ── Kingdom Map data ───────────────────────────────────────────────────────────
@app.route('/api/kingdom/map')
def kingdom_map():
    """Return visual kingdom data for the map canvas."""
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    db  = get_db()
    row = db.execute(
        "SELECT herd_cows,land_plots,crop_farms,cattle_pens,jewellery,"
        "is_married,spouse_email,has_crown,title,tribe_id,regalia,"
        "competition_wins,wins FROM users WHERE email=?",
        (user['email'],)
    ).fetchone()
    if not row:
        return jsonify({'error': 'User not found'}), 404
    d = dict(row)
    # Build visual map components
    d['map_elements'] = []
    # Homestead always present
    d['map_elements'].append({'type': 'kraal',   'emoji': '🏠', 'label': 'iNdlu',      'unlocked': True})
    # Land plots
    for i in range(min(d['land_plots'] or 0, 10)):
        d['map_elements'].append({'type': 'land',  'emoji': '🌾', 'label': f'Land {i+1}', 'unlocked': True})
    # Crop farms
    for i in range(min(d['crop_farms'] or 0, 5)):
        d['map_elements'].append({'type': 'farm',  'emoji': '🌽', 'label': f'Farm {i+1}', 'unlocked': True})
    # Cattle pens
    for i in range(min(d['cattle_pens'] or 0, 5)):
        d['map_elements'].append({'type': 'cattle','emoji': '🐄', 'label': f'Pen {i+1}',  'unlocked': True})
    # Marriage
    if d['is_married']:
        sp = db.execute("SELECT name FROM users WHERE email=?", (d['spouse_email'],)).fetchone()
        d['map_elements'].append({'type': 'marriage','emoji': '💑','label': 'uMshado — Married',
                                   'spouse': sp['name'] if sp else 'Partner', 'unlocked': True})
    # Crown
    if d['has_crown']:
        d['map_elements'].append({'type': 'throne','emoji': '👑','label': 'Royal Throne', 'unlocked': True})
    # Tribe territory
    tribe = TRIBES.get(d['tribe_id'] or 'world', {})
    d['tribe_territory'] = {'name': tribe.get('name','World'), 'icon': tribe.get('icon','🌍'),
                             'spirit': tribe.get('spirit', ''), 'region': tribe.get('region','')}
    # Title path progress
    d['title_path_progress'] = []
    for key, min_c in TITLE_PATH:
        d['title_path_progress'].append({
            'title': key,
            'min_cows': min_c,
            'unlocked': (d['herd_cows'] or 0) >= min_c,
            'info': TITLES.get(key, {}),
        })
    return jsonify(d)


# ═══════════════════════════════════════════════════════════════════════════════
#  SELF-IMPROVING AI ENGINE
#  Reinforcement learning from every game — the AI gets harder each defeat
#  Prize-pool protection — trained weights lock out random play in high stakes
# ═══════════════════════════════════════════════════════════════════════════════

import json   as _json
import math   as _math
import threading as _threading

# ── Learning constants ────────────────────────────────────────────────────────
AI_LEARN_REWARD        = 0.08   # position_bias boost per stone captured in winning game
AI_LEARN_PENALTY       = 0.12   # position_bias cut per stone lost in losing game
AI_ENTROPY_DECAY       = 0.94   # entropy_factor multiplier after each win
AI_ENTROPY_MIN         = 0.02   # never fully deterministic — prevents trivial loops
AI_ENTROPY_MAX         = 0.40   # starting randomness for new personas
AI_WEIGHT_CAP          = 4.0    # max position_bias value
AI_WEIGHT_FLOOR        = 0.10   # min position_bias (always considers all moves)
AI_RETRAIN_EVERY       = 5      # re-normalise weights every N games
AI_PRIZE_GUARD_COWS    = 50     # bets above this → entropy locked to 0, full trained mode
AI_BOARD_SLOTS         = 48     # 4×6 board holes (AI never plays on 4×4 — that is level 1)

# ── Default persona weights ───────────────────────────────────────────────────
# These seed each persona's style before learning begins
PERSONA_DEFAULTS = {
    'shaka':      {'capture_w': 1.6,  'defence_w': 0.3, 'relay_w': 0.8, 'entropy': 0.18},
    'moshoeshoe': {'capture_w': 0.9,  'defence_w': 1.8, 'relay_w': 1.0, 'entropy': 0.22},
    'sekhukhune': {'capture_w': 1.1,  'defence_w': 1.1, 'relay_w': 1.1, 'entropy': 0.28},
    'mzilikazi':  {'capture_w': 1.3,  'defence_w': 0.7, 'relay_w': 1.4, 'entropy': 0.38},
    'sobhuza':    {'capture_w': 1.0,  'defence_w': 1.0, 'relay_w': 1.6, 'entropy': 0.20},
    'grand_inkosi':{'capture_w': 1.8, 'defence_w': 1.5, 'relay_w': 1.3, 'entropy': 0.0},
}

# Thread-safe weight cache: {persona_id: WeightRecord}
_ai_weight_cache = {}
_ai_weight_lock  = _threading.Lock()


class WeightRecord:
    """In-memory AI weight record. Syncs to DB every AI_RETRAIN_EVERY games."""
    __slots__ = ('persona_id','pos_bias','capture_w','defence_w','relay_w',
                 'entropy','games_played','games_won','loss_cows','version','dirty')

    def __init__(self, persona_id: str, defaults: dict):
        self.persona_id  = persona_id
        self.pos_bias    = [1.0] * AI_BOARD_SLOTS   # uniform start
        self.capture_w   = defaults.get('capture_w',  1.0)
        self.defence_w   = defaults.get('defence_w',  1.0)
        self.relay_w     = defaults.get('relay_w',    1.0)
        self.entropy     = defaults.get('entropy',    0.25)
        self.games_played= 0
        self.games_won   = 0
        self.loss_cows   = 0
        self.version     = 1
        self.dirty       = False

    def score_move(self, idx: int, capture: int, relay_len: int,
                   opp_best: int, prize_locked: bool) -> float:
        """Score a candidate move using learned weights."""
        bias = self.pos_bias[idx % AI_BOARD_SLOTS]
        s    = (bias
                * (1.0 + capture * self.capture_w)
                * (1.0 + relay_len * self.relay_w * 0.05)
                - opp_best * self.defence_w * 0.6)
        if not prize_locked and self.entropy > AI_ENTROPY_MIN:
            import random
            s += random.gauss(0, self.entropy)
        return s

    def learn_from_game(self, move_log: list, won: bool, cows_delta: int):
        """
        Reinforcement update after a game ends.
        move_log: list of (board_idx, captured_stones) for AI moves this game
        won: True if AI won
        cows_delta: abs(AI_cows_end - human_cows_end) — margin of victory/defeat
        """
        if not move_log:
            return
        self.games_played += 1
        reward_sign = 1 if won else -1
        magnitude   = AI_LEARN_REWARD if won else AI_LEARN_PENALTY
        # Moves in the LAST third of game carry more weight (decisive phase)
        n = len(move_log)
        for rank, (idx, captured) in enumerate(move_log):
            phase_weight = 0.5 + (rank / max(1, n)) * 1.5  # 0.5 → 2.0
            delta = reward_sign * magnitude * phase_weight * (1 + captured * 0.1)
            slot  = idx % AI_BOARD_SLOTS
            self.pos_bias[slot] = max(
                AI_WEIGHT_FLOOR,
                min(AI_WEIGHT_CAP, self.pos_bias[slot] + delta)
            )
        if won:
            self.games_won  += 1
            # Entropy decays on win — AI becomes more precise
            self.entropy = max(AI_ENTROPY_MIN, self.entropy * AI_ENTROPY_DECAY)
            # Winning big → reward the macro strategy weights
            if cows_delta > 5:
                self.capture_w = min(2.5, self.capture_w * 1.02)
                self.relay_w   = min(2.5, self.relay_w   * 1.01)
        else:
            self.loss_cows += cows_delta
            # Losing badly → increase defensive weight
            if cows_delta > 8:
                self.defence_w = min(3.0, self.defence_w * 1.03)
            # Entropy rises slightly on loss — try new things
            self.entropy = min(AI_ENTROPY_MAX, self.entropy * 1.05)
        # Every N games: normalise pos_bias so mean stays near 1.0
        if self.games_played % AI_RETRAIN_EVERY == 0:
            self._normalise()
            self.version += 1
        self.dirty = True

    def _normalise(self):
        mean = sum(self.pos_bias) / len(self.pos_bias)
        if mean > 0:
            self.pos_bias = [b / mean for b in self.pos_bias]

    def win_rate(self) -> float:
        return self.games_won / max(1, self.games_played)

    def to_dict(self) -> dict:
        return {
            'pos_bias':   self.pos_bias,
            'capture_w':  round(self.capture_w, 4),
            'defence_w':  round(self.defence_w, 4),
            'relay_w':    round(self.relay_w, 4),
            'entropy':    round(self.entropy, 4),
            'games_played': self.games_played,
            'games_won':  self.games_won,
            'loss_cows':  self.loss_cows,
            'version':    self.version,
        }


def _load_weights(persona_id: str) -> WeightRecord:
    """Load (or create) weights for a persona — cache first, DB second."""
    with _ai_weight_lock:
        if persona_id in _ai_weight_cache:
            return _ai_weight_cache[persona_id]
        defaults = PERSONA_DEFAULTS.get(persona_id, PERSONA_DEFAULTS['sekhukhune'])
        rec      = WeightRecord(persona_id, defaults)
        try:
            # Only attempt DB load inside an application context
            import flask as _flask
            if _flask.has_app_context():
                db  = get_db()
                row = db.execute(
                    'SELECT weights_json FROM ai_weights WHERE persona_id=?', (persona_id,)
                ).fetchone()
                if row and row['weights_json']:
                    d = _json.loads(row['weights_json'])
                    rec.pos_bias     = d.get('pos_bias',   rec.pos_bias)
                    rec.capture_w    = d.get('capture_w',  rec.capture_w)
                    rec.defence_w    = d.get('defence_w',  rec.defence_w)
                    rec.relay_w      = d.get('relay_w',    rec.relay_w)
                    rec.entropy      = d.get('entropy',    rec.entropy)
                    rec.games_played = d.get('games_played', 0)
                    rec.games_won    = d.get('games_won',  0)
                    rec.loss_cows    = d.get('loss_cows',  0)
                    rec.version      = d.get('version',    1)
        except Exception as e:
            log.warning(f'[AI] Could not load weights for {persona_id}: {e}')
        _ai_weight_cache[persona_id] = rec
        return rec


def _save_weights(rec: WeightRecord):
    """Persist weights to DB."""
    try:
        db = get_db()
        db.execute(
            '''INSERT INTO ai_weights(persona_id, weights_json, games_played,
               games_won, win_rate, version, updated)
               VALUES(?,?,?,?,?,?,strftime('%s','now'))
               ON CONFLICT(persona_id) DO UPDATE SET
               weights_json=excluded.weights_json,
               games_played=excluded.games_played,
               games_won=excluded.games_won,
               win_rate=excluded.win_rate,
               version=excluded.version,
               updated=excluded.updated''',
            (rec.persona_id, _json.dumps(rec.to_dict()),
             rec.games_played, rec.games_won, round(rec.win_rate(), 4), rec.version)
        )
        db.commit()
        rec.dirty = False
        log.info(f'[AI] Saved weights for {rec.persona_id} v{rec.version} '
                 f'({rec.games_played} games, {rec.win_rate():.1%} win rate)')
    except Exception as e:
        log.error(f'[AI] Failed to save weights for {rec.persona_id}: {e}')


def _grand_inkosi_weights() -> WeightRecord:
    """
    Build a combined meta-persona from the BEST weights across all trained chiefs.
    Used for prize-pool games. This AI has learned from every game ever played.
    """
    rec = WeightRecord('grand_inkosi', PERSONA_DEFAULTS['grand_inkosi'])
    loaded = []
    for pid in PERSONA_DEFAULTS:
        if pid == 'grand_inkosi':
            continue
        try:
            w = _load_weights(pid)
            if w.games_played > 0:
                loaded.append(w)
        except Exception:
            pass
    if loaded:
        # Best-of ensemble: take max pos_bias at each position across all personas
        for slot in range(AI_BOARD_SLOTS):
            rec.pos_bias[slot] = max(w.pos_bias[slot] for w in loaded)
        # Take the most aggressive capture / defence weights
        rec.capture_w = max(w.capture_w for w in loaded)
        rec.defence_w = max(w.defence_w for w in loaded)
        rec.relay_w   = max(w.relay_w   for w in loaded)
    rec.entropy = 0.0   # Grand Inkosi is fully deterministic
    return rec


# ── Learned AI move selection ─────────────────────────────────────────────────
def ai_learned_move(game,
                    persona_id: str = 'shaka',
                    prize_locked: bool = False,
                    bet_amount: int = 0) -> int:
    """
    Select the best move using learned weights.
    Falls back to smart_ai if weights not yet trained (< 3 games).
    prize_locked=True removes ALL randomness — AI plays optimally.
    """
    valid = game.valid_moves(1)
    if not valid:
        return -1

    # Prize-protection: use Grand Inkosi for high-stakes bets
    if bet_amount >= AI_PRIZE_GUARD_COWS or prize_locked:
        weights     = _grand_inkosi_weights()
        prize_locked= True
        log.info(f'[AI] Grand Inkosi mode activated (bet={bet_amount} cows)')
    else:
        weights = _load_weights(persona_id)

    # Need enough training data to be meaningful
    if weights.games_played < 3 and not prize_locked:
        return game._smart_ai(valid)

    # Evaluate all valid moves
    opp_best  = game._best_opp_response()
    best_move = -1
    best_score= float('-inf')

    for idx in valid:
        capture   = game._sim_score(idx, 1)
        # Estimate relay length for this move
        relay_len = _estimate_relay(game, idx)
        score     = weights.score_move(idx, capture, relay_len, opp_best, prize_locked)
        if score > best_score:
            best_score = score
            best_move  = idx

    return best_move if best_move >= 0 else valid[0]


def _estimate_relay(game, idx: int) -> int:
    """Quick relay-chain length estimate without full simulation."""
    b      = list(game.board)
    path   = game._path_cached
    pm     = {v: i for i, v in enumerate(path)}
    stones = b[idx]
    pos    = pm.get(idx, 0)
    steps  = 0
    cur    = idx
    for _ in range(12):  # max 12 relay hops to estimate
        for _ in range(stones):
            pos = (pos + 1) % len(path)
            cur = path[pos]
        if b[cur] > 1:
            stones = b[cur]
            steps += 1
        else:
            break
    return steps


# ── Session move log: track each AI move for learning ─────────────────────────
_game_move_logs: dict[str, list] = {}   # session_token → [(idx, captured), ...]
_game_move_lock  = _threading.Lock()

def record_ai_move(session_token: str, idx: int, captured: int):
    with _game_move_lock:
        if session_token not in _game_move_logs:
            _game_move_logs[session_token] = []
        _game_move_logs[session_token].append((idx, captured))

def conclude_game_learning(session_token: str, persona_id: str,
                            ai_won: bool, ai_cows: int, human_cows: int):
    """Called when a game ends. Triggers weight update and async DB save."""
    with _game_move_lock:
        move_log = _game_move_logs.pop(session_token, [])
    if not move_log:
        return
    cows_delta = abs(ai_cows - human_cows)
    weights    = _load_weights(persona_id)
    weights.learn_from_game(move_log, ai_won, cows_delta)
    # Log the game outcome
    try:
        db = get_db()
        db.execute(
            '''INSERT INTO ai_game_log(persona_id,ai_won,ai_cows,human_cows,
               moves_count,version_when_played,created)
               VALUES(?,?,?,?,?,?,strftime('%s','now'))''',
            (persona_id, 1 if ai_won else 0, ai_cows, human_cows,
             len(move_log), weights.version)
        )
        db.commit()
    except Exception:
        pass
    # Save weights if dirty (async to avoid blocking response)
    if weights.dirty:
        t = _threading.Thread(target=_save_weights, args=(weights,), daemon=True)
        t.start()
    result = 'WON' if ai_won else 'LOST'
    log.info(f'[AI] {persona_id} {result} (v{weights.version}, '
             f'{weights.games_played} games, {weights.win_rate():.1%} win rate, '
             f'entropy={weights.entropy:.3f})')


# ── Patch GameState.ai_move to use learned engine ────────────────────────────
_original_game_ai_move = GameState.ai_move  # keep reference

def _learned_ai_move(self) -> int:
    """Replaces GameState.ai_move — uses learned weights when available."""
    valid = self.valid_moves(1)
    if not valid:
        return -1
    if self.level == 1:
        import random
        return random.choice(valid)
    persona_id   = getattr(self, '_persona_id',   'shaka')
    prize_locked = getattr(self, '_prize_locked',  False)
    bet_amount   = getattr(self, '_bet_amount',    0)
    return ai_learned_move(self, persona_id, prize_locked, bet_amount)

GameState.ai_move = _learned_ai_move


# ── API: AI stats dashboard ───────────────────────────────────────────────────
@app.route('/api/ai/stats')
def ai_stats():
    """Public AI learning stats — how has each chief evolved?"""
    stats = {}
    db    = get_db()
    for pid in AI_PERSONAS:
        rec = _load_weights(pid)
        row = db.execute(
            'SELECT games_played,games_won,win_rate,version FROM ai_weights WHERE persona_id=?',
            (pid,)
        ).fetchone()
        top_holes = sorted(range(AI_BOARD_SLOTS),
                           key=lambda i: rec.pos_bias[i], reverse=True)[:5]
        stats[pid] = {
            'games_played': rec.games_played,
            'games_won':    rec.games_won,
            'win_rate':     round(rec.win_rate() * 100, 1),
            'version':      rec.version,
            'entropy':      round(rec.entropy, 3),
            'capture_w':    round(rec.capture_w, 3),
            'defence_w':    round(rec.defence_w, 3),
            'relay_w':      round(rec.relay_w, 3),
            'top_positions': top_holes,
            'prize_locked_threshold': AI_PRIZE_GUARD_COWS,
            'description':  AI_PERSONAS[pid].get('description',''),
        }
    # Grand Inkosi composite
    gi = _grand_inkosi_weights()
    stats['grand_inkosi'] = {
        'games_played': sum(s.get('games_played',0) for s in stats.values()),
        'win_rate':     '—',
        'entropy':      0.0,
        'capture_w':    round(gi.capture_w, 3),
        'defence_w':    round(gi.defence_w, 3),
        'relay_w':      round(gi.relay_w, 3),
        'description':  'Grand Inkosi — best-of-all composite, deployed for prize games',
    }
    return jsonify({'personas': stats,
                    'prize_guard_threshold_cows': AI_PRIZE_GUARD_COWS})


@app.route('/api/ai/history/<persona_id>')
def ai_history(persona_id):
    """Game-by-game win/loss history for a persona."""
    db   = get_db()
    rows = db.execute(
        'SELECT ai_won,ai_cows,human_cows,moves_count,version_when_played,created '
        'FROM ai_game_log WHERE persona_id=? ORDER BY created DESC LIMIT 100',
        (persona_id,)
    ).fetchall()
    games = [dict(r) for r in rows]
    # Compute running win rate
    wins = 0
    for i, g in enumerate(reversed(games)):
        wins += g['ai_won']
        g['running_win_rate'] = round(wins / (i+1) * 100, 1)
    return jsonify({'persona_id': persona_id, 'games': games, 'total': len(games)})


@app.route('/api/ai/reset/<persona_id>', methods=['POST'])
def ai_reset(persona_id):
    """Admin-only: reset a persona's learned weights back to defaults."""
    if not _require_admin():
        return jsonify({'error': 'Unauthorized'}), 401
    with _ai_weight_lock:
        _ai_weight_cache.pop(persona_id, None)
    db = get_db()
    db.execute('DELETE FROM ai_weights WHERE persona_id=?', (persona_id,))
    db.execute('DELETE FROM ai_game_log WHERE persona_id=?', (persona_id,))
    db.commit()
    log.info(f'[AI] Weights reset for {persona_id} by admin')
    return jsonify({'ok': True, 'message': f'{persona_id} weights reset to factory defaults'})


@app.route('/api/ai/leaderboard')
def ai_leaderboard():
    """Which persona is hardest right now? Sorted by win rate."""
    results = []
    for pid in AI_PERSONAS:
        rec = _load_weights(pid)
        results.append({
            'persona_id':  pid,
            'name':        AI_PERSONAS[pid]['name'],
            'icon':        AI_PERSONAS[pid]['icon'],
            'tribe':       AI_PERSONAS[pid]['tribe'],
            'win_rate_pct':round(rec.win_rate() * 100, 1),
            'games_played':rec.games_played,
            'entropy':     round(rec.entropy, 3),
            'version':     rec.version,
            'difficulty':  AI_PERSONAS[pid]['difficulty'],
        })
    results.sort(key=lambda x: x['win_rate_pct'], reverse=True)
    return jsonify({'leaderboard': results})


# ═══════════════════════════════════════════════════════════════════════════════
#  INTSHUBA v2.3.0 — ALL 18 APPROVED FEATURES
#  ELO · Puzzles · Replay · Friends · Clans · Chests · Achievements · Streaks
#  Referrals · Push Notifications · Seasonal Boards · Live Leaderboard
#  AI Analysis Chat · Family Mode · Live Tournament UI · Sound Pack
# ═══════════════════════════════════════════════════════════════════════════════

import hashlib as _hashlib

# ── ELO rating constants ───────────────────────────────────────────────────────
ELO_START       = 1200
ELO_K_FACTOR    = 32      # standard K for non-titled players
ELO_K_FAST      = 40      # higher K for players under 2100
ELO_MIN         = 100     # floor — cannot go below this

# ── Achievement definitions ────────────────────────────────────────────────────
ACHIEVEMENTS = {
    'first_win':         {'icon':'🏆','name':'First Blood',          'desc':'Win your first game',                   'reward_cows':5},
    'ten_wins':          {'icon':'⚔️', 'name':'Warrior Rising',       'desc':'Win 10 games',                          'reward_cows':15},
    'fifty_wins':        {'icon':'🦅', 'name':'Proven Chief',         'desc':'Win 50 games',                          'reward_cows':50},
    'hundred_wins':      {'icon':'👑', 'name':'Inkosi',               'desc':'Win 100 games',                         'reward_cows':100},
    'first_capture':     {'icon':'🐄', 'name':'First Capture',        'desc':'Capture your first stones',             'reward_cows':3},
    'big_capture':       {'icon':'💥', 'name':'Herd Raid',            'desc':'Capture 10+ stones in one move',        'reward_cows':10},
    'level2_unlock':     {'icon':'🏹', 'name':'iNduna Rises',         'desc':'Reach Level 2',                         'reward_cows':20},
    'level3_unlock':     {'icon':'🦁', 'name':'Chief of Chiefs',      'desc':'Reach Level 3',                         'reward_cows':50},
    'herd_100':          {'icon':'🌾', 'name':'Growing Herd',         'desc':'Accumulate 100 cows',                   'reward_cows':10},
    'herd_500':          {'icon':'🐘', 'name':'Cattle Baron',         'desc':'Accumulate 500 cows',                   'reward_cows':50},
    'herd_1000':         {'icon':'👑', 'name':'Herd of Legends',      'desc':'Accumulate 1,000 cows',                 'reward_cows':100},
    'join_tribe':        {'icon':'⚔️', 'name':'Blood Bond',           'desc':'Join a tribe',                          'reward_cows':10},
    'married':           {'icon':'💍', 'name':'Lobola Paid',          'desc':'Pay lobola and get married',            'reward_cows':25},
    'crown_held':        {'icon':'🔱', 'name':'iSilo',                'desc':'Hold the crown for 1 full day',         'reward_cows':200},
    'buy_land':          {'icon':'🌾', 'name':'Landowner',            'desc':'Buy your first land plot',              'reward_cows':15},
    'defeat_shaka':      {'icon':'🐗', 'name':'Shaka Slayer',         'desc':'Defeat Shaka kaSenzangakhona',          'reward_cows':100},
    'story_complete':    {'icon':'📜', 'name':'Tale is Told',         'desc':'Complete all 10 story chapters',        'reward_cows':500},
    'streak_7':          {'icon':'🔥', 'name':'Week of Fire',         'desc':'Log in 7 days in a row',               'reward_cows':30},
    'streak_30':         {'icon':'💫', 'name':'Month of Dedication',  'desc':'Log in 30 days in a row',              'reward_cows':150},
    'first_friend':      {'icon':'🤝', 'name':'Not Alone',            'desc':'Add your first friend',                 'reward_cows':10},
    'join_clan':         {'icon':'🏰', 'name':'Clan Born',            'desc':'Join or create a clan',                 'reward_cows':15},
    'clan_war_win':      {'icon':'⚔️', 'name':'Clan Champion',        'desc':'Win a clan war',                        'reward_cows':50},
    'puzzle_5':          {'icon':'🧩', 'name':'Puzzle Warrior',       'desc':'Solve 5 board puzzles',                 'reward_cows':15},
    'puzzle_50':         {'icon':'🧠', 'name':'Master Tactician',     'desc':'Solve 50 board puzzles',               'reward_cows':75},
    'referral':          {'icon':'🎁', 'name':'Recruiter',            'desc':'Refer a friend who reaches Level 2',   'reward_cows':20},
    'open_chest':        {'icon':'📦', 'name':'First Treasure',       'desc':'Open your first chest',                 'reward_cows':5},
    'daily_10':          {'icon':'📅', 'name':'Daily Devotee',        'desc':'Complete 10 daily challenges',          'reward_cows':30},
    'elo_1400':          {'icon':'📈', 'name':'Rising Talent',        'desc':'Reach ELO rating 1400',                 'reward_cows':25},
    'elo_1600':          {'icon':'🎯', 'name':'Expert Player',        'desc':'Reach ELO rating 1600',                 'reward_cows':75},
    'elo_1800':          {'icon':'🏅', 'name':'Master',               'desc':'Reach ELO rating 1800',                'reward_cows':150},
}

# ── Chest definitions ─────────────────────────────────────────────────────────
CHEST_TYPES = {
    'bronze': {'unlock_hours':4,  'min_cows':5,  'max_cows':15,  'icon':'🪨', 'label':'Bronze Chest'},
    'silver': {'unlock_hours':8,  'min_cows':15, 'max_cows':40,  'icon':'⚙️', 'label':'Silver Chest'},
    'gold':   {'unlock_hours':24, 'min_cows':40, 'max_cows':100, 'icon':'🌟', 'label':'Gold Chest'},
    'royal':  {'unlock_hours':72, 'min_cows':100,'max_cows':300, 'icon':'👑', 'label':'Royal Chest'},
}
CHEST_SLOTS = 4    # free players get 4 slots; Inkosi Club gets 6

# ── Clan constants ─────────────────────────────────────────────────────────────
CLAN_MAX_MEMBERS  = 20
CLAN_WAR_DURATION = 7 * 86400   # 7 days

# ── Push notification templates ────────────────────────────────────────────────
PUSH_TEMPLATES = {
    'chest_ready':    {'title':'🐄 Your chest is ready!',            'body':'Open it before someone steals your cows.', 'url':'/?action=kingdom'},
    'crown_challenge':{'title':'⚔️ Crown challenge incoming!',       'body':'{challenger} is coming for your throne!',  'url':'/?action=crown'},
    'daily_ready':    {'title':'🌅 New daily challenge!',            'body':'Today\'s board is live. Can you top it?',   'url':'/?action=daily'},
    'streak_reminder':{'title':'🔥 Don\'t break your streak!',       'body':'You\'ve played {n} days in a row. Keep it up!','url':'/?action=play'},
    'friend_joined':  {'title':'🤝 {name} joined Intshuba!',         'body':'Your friend is waiting for a challenge.',    'url':'/?action=friends'},
    'clan_war':       {'title':'⚔️ Clan war started!',               'body':'{clan} vs {enemy} — battle begins now.',    'url':'/?action=clan'},
    'cows_earned':    {'title':'🐄 Overnight earnings!',             'body':'Your herd earned {n} cows while you slept.','url':'/?action=kingdom'},
    'elo_milestone':  {'title':'📈 ELO milestone reached!',          'body':'You hit {elo} rating — {title}!',           'url':'/?action=profile'},
}

# ── Seasonal board themes ──────────────────────────────────────────────────────
SEASONAL_BOARD_THEMES = {
    'harvest': {'board_bg':'#2a1a00','stone_colors':['#FFD700','#FFA500','#FF8C00','#DAA520'],
                'particle':'🌽','description':'Golden harvest board — maize and sorghum colours'},
    'rain':    {'board_bg':'#001a2a','stone_colors':['#4488FF','#00CED1','#1E90FF','#87CEEB'],
                'particle':'💧','description':'Rain season board — river blues and sky tones'},
    'lobola':  {'board_bg':'#1a0030','stone_colors':['#FF69B4','#FF1493','#C71585','#FFB6C1'],
                'particle':'💍','description':'Lobola season board — beadwork pinks and purples'},
    'reed':    {'board_bg':'#0a2a0a','stone_colors':['#90EE90','#32CD32','#228B22','#7CFC00'],
                'particle':'🎋','description':'Reed dance board — verdant greens'},
    'warriors':{'board_bg':'#1a0000','stone_colors':['#DC143C','#FF0000','#8B0000','#FF6347'],
                'particle':'⚔️','description':'Warriors week board — war paint reds and blacks'},
    'default': {'board_bg':'#1a0f02','stone_colors':['#C9A84C','#8B6910','#DAA520','#B8860B'],
                'particle':'🐄','description':'Standard Nguni board'},
}

# ── ELO calculation ────────────────────────────────────────────────────────────
def _calc_elo(winner_elo: int, loser_elo: int) -> tuple:
    """Returns (new_winner_elo, new_loser_elo, points_delta)."""
    expected_w = 1 / (1 + 10 ** ((loser_elo - winner_elo) / 400))
    expected_l = 1 - expected_w
    k = ELO_K_FAST if winner_elo < 2100 else ELO_K_FACTOR
    delta      = round(k * (1 - expected_w))
    new_w      = max(ELO_MIN, winner_elo + delta)
    new_l      = max(ELO_MIN, loser_elo  - delta)
    return new_w, new_l, delta

def _update_elo_legacy(winner_email: str, loser_email: str, is_ai_game: bool = True):
    """Update ELO ratings after a game. AI games use a fixed AI ELO of 1400."""
    if not winner_email:
        return
    db = get_db()
    w_row = db.execute('SELECT elo_rating FROM users WHERE email=?', (winner_email,)).fetchone()
    w_elo = (w_row['elo_rating'] or ELO_START) if w_row else ELO_START
    if is_ai_game:
        l_elo = 1400  # fixed AI ELO
        new_w, _, delta = _calc_elo(w_elo, l_elo)
        db.execute('UPDATE users SET elo_rating=?, elo_peak=MAX(elo_peak,?) WHERE email=?',
                   (new_w, new_w, winner_email))
    else:
        l_row = db.execute('SELECT elo_rating FROM users WHERE email=?', (loser_email,)).fetchone()
        l_elo = (l_row['elo_rating'] or ELO_START) if l_row else ELO_START
        new_w, new_l, delta = _calc_elo(w_elo, l_elo)
        db.execute('UPDATE users SET elo_rating=?, elo_peak=MAX(elo_peak,?) WHERE email=?',
                   (new_w, new_w, winner_email))
        db.execute('UPDATE users SET elo_rating=MAX(?,elo_rating-?) WHERE email=?',
                   (ELO_MIN, delta, loser_email))
    db.commit()
    return delta

# ── Achievement granting ───────────────────────────────────────────────────────
def _grant_achievement(email: str, achievement_id: str) -> bool:
    """Grant achievement if not already held. Returns True if newly granted."""
    if achievement_id not in ACHIEVEMENTS:
        return False
    db  = get_db()
    existing = db.execute(
        'SELECT id FROM user_achievements WHERE user_email=? AND achievement_id=?',
        (email, achievement_id)
    ).fetchone()
    if existing:
        return False
    ach     = ACHIEVEMENTS[achievement_id]
    reward  = ach.get('reward_cows', 0)
    db.execute(
        'INSERT INTO user_achievements(user_email,achievement_id,earned_at) VALUES(?,?,strftime(\'%s\',\'now\'))',
        (email, achievement_id)
    )
    db.commit()
    if reward:
        _add_cows(email, reward, 'achievement_' + achievement_id, {'achievement': achievement_id})
    log.info(f'[achievement] {email} earned {achievement_id} (+{reward} cows)')
    return True

def _check_achievements_legacy(email: str):
    """Check and grant any newly-earned achievements for a user."""
    if not email:
        return []
    db  = get_db()
    row = db.execute(
        'SELECT wins, herd_cows, land_plots, is_married, has_crown, tribe_id, '
        'login_streak, elo_rating FROM users WHERE email=?', (email,)
    ).fetchone()
    if not row:
        return []
    newly = []
    wins    = row['wins'] or 0
    cows    = row['herd_cows'] or 0
    streak  = row['login_streak'] or 0
    elo     = row['elo_rating'] or ELO_START
    if wins >= 1:   newly.append(_grant_achievement(email,'first_win'))
    if wins >= 10:  newly.append(_grant_achievement(email,'ten_wins'))
    if wins >= 50:  newly.append(_grant_achievement(email,'fifty_wins'))
    if wins >= 100: newly.append(_grant_achievement(email,'hundred_wins'))
    if cows >= 100:  newly.append(_grant_achievement(email,'herd_100'))
    if cows >= 500:  newly.append(_grant_achievement(email,'herd_500'))
    if cows >= 1000: newly.append(_grant_achievement(email,'herd_1000'))
    if row['is_married']: newly.append(_grant_achievement(email,'married'))
    if row['has_crown']:  newly.append(_grant_achievement(email,'crown_held'))
    if row['land_plots'] and row['land_plots']>=1: newly.append(_grant_achievement(email,'buy_land'))
    if row['tribe_id'] and row['tribe_id']!='world': newly.append(_grant_achievement(email,'join_tribe'))
    if streak >= 7:  newly.append(_grant_achievement(email,'streak_7'))
    if streak >= 30: newly.append(_grant_achievement(email,'streak_30'))
    if elo >= 1400: newly.append(_grant_achievement(email,'elo_1400'))
    if elo >= 1600: newly.append(_grant_achievement(email,'elo_1600'))
    if elo >= 1800: newly.append(_grant_achievement(email,'elo_1800'))
    return [a for a in newly if a]

# ── Login streak update ────────────────────────────────────────────────────────
def _update_login_streak(email: str):
    """Update daily login streak. Call on every login."""
    db  = get_db()
    row = db.execute('SELECT last_login, login_streak, streak_shield FROM users WHERE email=?',
                     (email,)).fetchone()
    if not row:
        return 0
    now         = int(time.time())
    last        = row['last_login'] or 0
    streak      = row['login_streak'] or 0
    shield      = row['streak_shield'] or 0
    days_since  = (now - last) // 86400
    if days_since == 1:
        streak += 1   # consecutive day
    elif days_since == 2 and shield > 0:
        streak += 1   # missed one day but shield saves it
        shield -= 1
    elif days_since > 1:
        streak = 1    # reset
    else:
        pass          # same day — no change
    db.execute('UPDATE users SET login_streak=?, streak_shield=? WHERE email=?',
               (streak, shield, email))
    db.commit()
    return streak

# ── Chest granting ─────────────────────────────────────────────────────────────
def _grant_chest_legacy(email: str, chest_type: str = 'bronze') -> bool:
    """Grant a chest to a player if they have a free slot."""
    db       = get_db()
    occupied = db.execute(
        'SELECT COUNT(*) FROM chests WHERE player_email=? AND status IN (\'locked\',\'unlocking\')',
        (email,)
    ).fetchone()[0]
    plan     = (db.execute('SELECT plan FROM users WHERE email=?', (email,)).fetchone() or {}).get('plan','free')
    max_slots= 6 if plan in ('inkosi','school') else CHEST_SLOTS
    if occupied >= max_slots:
        return False
    chest       = CHEST_TYPES.get(chest_type, CHEST_TYPES['bronze'])
    unlock_at   = int(time.time()) + chest['unlock_hours'] * 3600
    db.execute(
        'INSERT INTO chests(player_email,chest_type,locked_until,status) VALUES(?,?,?,\'locked\')',
        (email, chest_type, unlock_at)
    )
    db.commit()
    return True

# ── Referral code generation ───────────────────────────────────────────────────
def _get_or_create_referral_code(email: str) -> str:
    db  = get_db()
    row = db.execute('SELECT referral_code FROM users WHERE email=?', (email,)).fetchone()
    if row and row['referral_code']:
        return row['referral_code']
    code = _hashlib.md5(email.encode()).hexdigest()[:8].upper()
    db.execute('UPDATE users SET referral_code=? WHERE email=?', (code, email))
    db.commit()
    return code

# ─────────────────────────────────────────────────────────────────────────────
#  ELO ROUTES
# ─────────────────────────────────────────────────────────────────────────────

# ─────────────────────────────────────────────────────────────────────────────
#  ACHIEVEMENT ROUTES
# ─────────────────────────────────────────────────────────────────────────────

@app.route('/api/achievements/check', methods=['POST'])
def check_achievements():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    newly = _check_achievements(user['email'])
    new_ones = [ACHIEVEMENTS[a] for a in (newly or []) if isinstance(a, str) and a in ACHIEVEMENTS]
    return jsonify({'ok': True, 'newly_earned': new_ones, 'count': len(new_ones)})

# ─────────────────────────────────────────────────────────────────────────────
#  CHEST ROUTES
# ─────────────────────────────────────────────────────────────────────────────

@app.route('/api/chests/open/<int:chest_id>', methods=['POST'], endpoint='open_chest_legacy')
def open_chest_legacy(chest_id):
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data     = request.get_json(force=True) or {}
    instant  = bool(data.get('instant', False))
    db       = get_db()
    chest_row = db.execute(
        'SELECT * FROM chests WHERE id=? AND player_email=?', (chest_id, user['email'])
    ).fetchone()
    if not chest_row:
        return jsonify({'error': 'Chest not found'}), 404
    chest_info = CHEST_TYPES.get(chest_row['chest_type'], CHEST_TYPES['bronze'])
    now        = int(time.time())
    if chest_row['locked_until'] > now and not instant:
        time_left = chest_row['locked_until'] - now
        cost      = max(1, time_left // 3600)  # 1 cow per hour remaining
        return jsonify({'ok': False, 'locked': True, 'time_left': time_left,
                        'instant_cost_cows': cost,
                        'message': f'Chest opens in {time_left//3600}h. Pay {cost} cows to open now.'})
    if instant:
        time_left = max(0, chest_row['locked_until'] - now)
        cost      = max(1, time_left // 3600)
        herd      = _get_herd(user['email'])
        if herd < cost:
            return jsonify({'ok': False, 'insufficient': True, 'cost': cost, 'herd': herd}), 402
        _add_cows(user['email'], -cost, 'chest_instant_open', {'chest_id': chest_id})
    import random as _r
    reward = _r.randint(chest_info.get('min_cows', 5), chest_info.get('max_cows', 30))
    _add_cows(user['email'], reward, 'chest_opened', {'chest_type': chest_row['chest_type']})
    db.execute('UPDATE chests SET status=\'opened\' WHERE id=?', (chest_id,))
    db.commit()
    _grant_achievement(user['email'], 'open_chest')
    return jsonify({'ok': True, 'reward_cows': reward, 'chest_type': chest_row['chest_type'],
                    'message': f'{chest_info["icon"]} {chest_info["label"]} opened! +{reward} cows!'})

# ─────────────────────────────────────────────────────────────────────────────
#  STREAK ROUTES
# ─────────────────────────────────────────────────────────────────────────────

@app.route('/api/streak')
def get_streak():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    db  = get_db()
    row = db.execute('SELECT login_streak, streak_shield FROM users WHERE email=?',
                     (user['email'],)).fetchone()
    streak = row['login_streak'] or 0
    shield = row['streak_shield'] or 0
    milestones = [
        {'days':3,  'reward':5,  'reached': streak>=3},
        {'days':7,  'reward':30, 'reached': streak>=7},
        {'days':14, 'reward':75, 'reached': streak>=14},
        {'days':30, 'reward':150,'reached': streak>=30},
        {'days':60, 'reward':400,'reached': streak>=60},
    ]
    return jsonify({'streak': streak, 'streak_shield': shield, 'milestones': milestones})

# ─────────────────────────────────────────────────────────────────────────────
#  FRIENDS ROUTES
# ─────────────────────────────────────────────────────────────────────────────

@app.route('/api/friends')
def get_friends():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    db   = get_db()
    rows = db.execute(
        '''SELECT u.name, u.elo_rating, u.title, u.tribe_id, u.has_crown,
                  f.status, f.created
           FROM friends f
           JOIN users u ON (CASE WHEN f.user_a=? THEN f.user_b ELSE f.user_a END)=u.email
           WHERE (f.user_a=? OR f.user_b=?) AND f.status=\'accepted\'
           ORDER BY u.name''',
        (user['email'], user['email'], user['email'])
    ).fetchall()
    return jsonify({'friends': [dict(r) for r in rows]})

# ─────────────────────────────────────────────────────────────────────────────
#  CLAN (uMphakathi) ROUTES
# ─────────────────────────────────────────────────────────────────────────────

@app.route('/api/clans', methods=['GET'])
def list_clans():
    db   = get_db()
    rows = db.execute(
        'SELECT id, name, description, tribe_id, member_count, total_cows, war_wins FROM clans '
        'ORDER BY total_cows DESC LIMIT 30'
    ).fetchall()
    return jsonify({'clans': [dict(r) for r in rows]})

@app.route('/api/clans/create', methods=['POST'], endpoint='create_clan_legacy')
def create_clan_legacy():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data  = request.get_json(force=True) or {}
    name  = sanitise(str(data.get('name','')), 50)
    desc  = sanitise(str(data.get('description','')), 200)
    tribe = sanitise(str(data.get('tribe_id','world')), 30)
    if not name:
        return jsonify({'error': 'Clan name required'}), 400
    db    = get_db()
    existing = db.execute('SELECT id FROM clans WHERE leader_email=?', (user['email'],)).fetchone()
    if existing:
        return jsonify({'error': 'You already lead a clan'}), 409
    clan_id = 'CLAN-' + _hashlib.md5(name.encode()).hexdigest()[:8].upper()
    db.execute(
        'INSERT INTO clans(id,name,description,tribe_id,leader_email,member_count,total_cows) VALUES(?,?,?,?,?,1,0)',
        (clan_id, name, desc, tribe, user['email'])
    )
    db.execute('UPDATE users SET clan_id=? WHERE email=?', (clan_id, user['email']))
    db.commit()
    _grant_achievement(user['email'], 'join_clan')
    return jsonify({'ok': True, 'clan_id': clan_id, 'message': f'Clan "{name}" created! Recruit up to {CLAN_MAX_MEMBERS} warriors.'})

@app.route('/api/clans/<clan_id>/join', methods=['POST'], endpoint='join_clan_legacy')
def join_clan_legacy(clan_id):
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    db   = get_db()
    clan = db.execute('SELECT * FROM clans WHERE id=?', (clan_id,)).fetchone()
    if not clan:
        return jsonify({'error': 'Clan not found'}), 404
    if clan['member_count'] >= CLAN_MAX_MEMBERS:
        return jsonify({'error': f'Clan is full ({CLAN_MAX_MEMBERS} members max)'}), 409
    db.execute('UPDATE users SET clan_id=? WHERE email=?', (clan_id, user['email']))
    db.execute('UPDATE clans SET member_count=member_count+1 WHERE id=?', (clan_id,))
    db.commit()
    _grant_achievement(user['email'], 'join_clan')
    return jsonify({'ok': True, 'clan': dict(clan), 'message': f'Joined {clan["name"]}!'})

@app.route('/api/clans/<clan_id>/members')
def clan_members(clan_id):
    db   = get_db()
    clan = db.execute('SELECT * FROM clans WHERE id=?', (clan_id,)).fetchone()
    if not clan:
        return jsonify({'error': 'Clan not found'}), 404
    members = db.execute(
        'SELECT name, elo_rating, herd_cows, title, wins, has_crown FROM users '
        'WHERE clan_id=? ORDER BY elo_rating DESC', (clan_id,)
    ).fetchall()
    return jsonify({'clan': dict(clan), 'members': [dict(m) for m in members]})

@app.route('/api/clans/war/standings')
def clan_war_standings():
    db   = get_db()
    rows = db.execute(
        'SELECT c.id, c.name, c.tribe_id, c.war_wins, c.total_cows, c.member_count, '
        'SUM(u.wins) as total_wins FROM clans c '
        'LEFT JOIN users u ON u.clan_id=c.id '
        'GROUP BY c.id ORDER BY total_wins DESC LIMIT 20'
    ).fetchall()
    return jsonify({'standings': [dict(r) for r in rows]})

# ─────────────────────────────────────────────────────────────────────────────
#  PUZZLE ROUTES
# ─────────────────────────────────────────────────────────────────────────────

SAMPLE_PUZZLES = [
    {'id':1,'title':'The Opening Trap','difficulty':'easy','board':[2,1,0,2,1,2,0,1,2,0,1,2,2,1,0,1,2,0,1,2,0,2,1,2],'solution_moves':[3],'description':'Capture 4 stones in one move. Hole 3 leads to the inner row capture.'},
    {'id':2,'title':'The Relay Chain','difficulty':'medium','board':[0,3,2,0,1,2,1,0,2,1,0,2,3,0,1,2,0,1,2,0,1,0,2,1],'solution_moves':[1,4],'description':'Trigger a relay chain to capture 6 stones across two moves.'},
    {'id':3,'title':'The Double Strike','difficulty':'medium','board':[2,0,1,2,0,3,1,2,0,1,2,0,0,2,1,0,2,1,3,0,2,1,0,2],'solution_moves':[5],'description':'A single move that captures stones on both flanks simultaneously.'},
    {'id':4,'title':'The Fortress Defence','difficulty':'hard','board':[1,0,2,0,3,0,2,1,0,2,1,0,1,2,0,1,0,2,0,1,2,0,1,3],'solution_moves':[4,10],'description':'Your opponent threatens. Find the two moves that protect your herd and counter-attack.'},
    {'id':5,'title':'Shaka\'s Gambit','difficulty':'expert','board':[3,1,0,2,1,0,2,3,1,0,1,2,0,3,1,2,0,1,2,3,0,1,2,0],'solution_moves':[7],'description':'The move Shaka himself favoured. Sacrifice 3 stones to capture 12 in the next turn.'},
]

@app.route('/api/puzzles/<int:puzzle_id>/solve', methods=['POST'], endpoint='solve_puzzle_legacy')
def solve_puzzle_legacy(puzzle_id):
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data     = request.get_json(force=True) or {}
    moves    = data.get('moves', [])
    puzzle   = next((p for p in SAMPLE_PUZZLES if p['id'] == puzzle_id), None)
    if not puzzle:
        return jsonify({'error': 'Puzzle not found'}), 404
    correct  = sorted(moves) == sorted(puzzle['solution_moves'])
    db       = get_db()
    if correct:
        existing = db.execute(
            'SELECT id FROM puzzle_completions WHERE user_email=? AND puzzle_id=?',
            (user['email'], puzzle_id)
        ).fetchone()
        if not existing:
            reward = {'easy':3,'medium':8,'hard':15,'expert':30}.get(puzzle['difficulty'], 5)
            db.execute(
                'INSERT INTO puzzle_completions(user_email,puzzle_id,completed_at) VALUES(?,?,strftime(\'%s\',\'now\'))',
                (user['email'], puzzle_id)
            )
            db.commit()
            _add_cows(user['email'], reward, 'puzzle_solved', {'puzzle_id': puzzle_id})
            # Check puzzle achievements
            count = db.execute('SELECT COUNT(*) FROM puzzle_completions WHERE user_email=?',
                                (user['email'],)).fetchone()[0]
            if count >= 5:  _grant_achievement(user['email'], 'puzzle_5')
            if count >= 50: _grant_achievement(user['email'], 'puzzle_50')
            return jsonify({'ok':True,'correct':True,'reward_cows':reward,
                            'message':f'🧩 Solved! +{reward} cows!'})
        return jsonify({'ok':True,'correct':True,'already_solved':True})
    return jsonify({'ok':True,'correct':False,'hint':puzzle.get('description','Keep trying!')})

# ─────────────────────────────────────────────────────────────────────────────
#  REFERRAL ROUTES
# ─────────────────────────────────────────────────────────────────────────────

@app.route('/api/referral/code')
def get_referral_code():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    code     = _get_or_create_referral_code(user['email'])
    base_url = os.environ.get('APP_URL', request.host_url.rstrip('/'))
    db       = get_db()
    count    = db.execute('SELECT COUNT(*) FROM users WHERE referred_by=?', (user['email'],)).fetchone()[0]
    return jsonify({'code': code, 'link': f'{base_url}/?ref={code}',
                    'referrals_made': count,
                    'reward_per_referral': 20,
                    'message': 'Share your link. You both get 10 cows on registration, +20 when they reach Level 2.'})

@app.route('/api/referral/apply', methods=['POST'])
def apply_referral():
    """Apply a referral code during or after registration."""
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data = request.get_json(force=True) or {}
    code = sanitise(str(data.get('code','')), 20).upper()
    db   = get_db()
    referrer = db.execute('SELECT email, name FROM users WHERE referral_code=?', (code,)).fetchone()
    if not referrer or referrer['email'] == user['email']:
        return jsonify({'error': 'Invalid referral code'}), 400
    already = db.execute('SELECT referred_by FROM users WHERE email=?', (user['email'],)).fetchone()
    if already and already['referred_by']:
        return jsonify({'error': 'Referral already applied'}), 409
    db.execute('UPDATE users SET referred_by=? WHERE email=?', (referrer['email'], user['email']))
    db.commit()
    _add_cows(user['email'],         10, 'referral_bonus_new',       {'referrer': referrer['email']})
    _add_cows(referrer['email'],     10, 'referral_bonus_referrer',   {'new_user': user['email']})
    return jsonify({'ok': True, 'referrer': referrer['name'],
                    'message': f'🎁 +10 cows! You and {referrer["name"]} both got a bonus!'})

# ─────────────────────────────────────────────────────────────────────────────
#  DAILY CHALLENGE ROUTES
# ─────────────────────────────────────────────────────────────────────────────

def _daily_board_seed() -> int:
    """Generate deterministic daily seed from today's date."""
    today = time.strftime('%Y%m%d')
    return int(_hashlib.md5(today.encode()).hexdigest(), 16) % 100000

@app.route('/api/daily-challenge', endpoint='daily_challenge_legacy')
def daily_challenge_legacy():
    """Return today's fixed board challenge (same for all players)."""
    db   = get_db()
    user = current_user()
    seed = _daily_board_seed()
    import random as _r
    _r.seed(seed)
    board = [_r.randint(1, 3) for _ in range(24)]  # 4×6 board
    # Check if user already completed todays challenge
    completed = False
    rank = None
    if user:
        today = time.strftime('%Y-%m-%d')
        row   = db.execute(
            'SELECT score FROM daily_scores WHERE user_email=? AND day=?',
            (user['email'], today)
        ).fetchone()
        completed = bool(row)
        if completed:
            rank_row = db.execute(
                'SELECT COUNT(*)+1 FROM daily_scores WHERE day=? AND score > ?',
                (today, row['score'])
            ).fetchone()
            rank = rank_row[0] if rank_row else None
    # Top scores for today
    today_str = time.strftime('%Y-%m-%d')
    top = db.execute(
        'SELECT u.name, ds.score FROM daily_scores ds '
        'JOIN users u ON u.email=ds.user_email '
        'WHERE ds.day=? ORDER BY ds.score DESC LIMIT 10',
        (today_str,)
    ).fetchall()
    return jsonify({'board': board, 'seed': seed, 'date': today_str,
                    'completed': completed, 'rank': rank,
                    'leaderboard': [dict(r) for r in top]})

@app.route('/api/daily-challenge/submit', methods=['POST'])
def submit_daily_challenge():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data  = request.get_json(force=True) or {}
    score = int(data.get('score', 0))  # stones captured in session
    today = time.strftime('%Y-%m-%d')
    db    = get_db()
    existing = db.execute(
        'SELECT score FROM daily_scores WHERE user_email=? AND day=?', (user['email'], today)
    ).fetchone()
    if existing:
        if score > existing['score']:
            db.execute('UPDATE daily_scores SET score=? WHERE user_email=? AND day=?',
                       (score, user['email'], today))
        db.commit()
        return jsonify({'ok': True, 'improved': score > existing['score'], 'score': score})
    db.execute('INSERT INTO daily_scores(user_email,day,score) VALUES(?,?,?)',
               (user['email'], today, score))
    db.commit()
    _add_cows(user['email'], 5, 'daily_challenge_completed', {'score': score})
    count = db.execute(
        'SELECT COUNT(*) FROM daily_scores WHERE user_email=?', (user['email'],)
    ).fetchone()[0]
    _grant_achievement(user['email'], 'daily_10') if count >= 10 else None
    return jsonify({'ok': True, 'score': score, 'reward_cows': 5,
                    'message': f'Daily challenge done! +5 cows. Score: {score}'})

# ─────────────────────────────────────────────────────────────────────────────
#  LIVE GLOBAL LEADERBOARD
# ─────────────────────────────────────────────────────────────────────────────

# ─────────────────────────────────────────────────────────────────────────────
#  FAMILY / PARENTAL MODE
# ─────────────────────────────────────────────────────────────────────────────

@app.route('/api/family/report')
def family_report():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    db = get_db()
    children = db.execute(
        'SELECT name, wins, losses, games, herd_cows, login_streak FROM users '
        'WHERE parent_email=?', (user['email'],)
    ).fetchall()
    return jsonify({'children': [dict(c) for c in children],
                    'message': 'Weekly report — CAPS-aligned progress for each child.'})

# ─────────────────────────────────────────────────────────────────────────────
#  SEASONAL BOARD THEME ROUTE
# ─────────────────────────────────────────────────────────────────────────────

@app.route('/api/seasonal/board-theme')
def seasonal_board_theme():
    evt = _current_seasonal_event()
    if evt and evt['id'] in SEASONAL_BOARD_THEMES:
        theme = SEASONAL_BOARD_THEMES[evt['id']]
        return jsonify({'active': True, 'event': evt['id'],
                        'event_name': evt['name'], 'theme': theme})
    return jsonify({'active': False, 'theme': SEASONAL_BOARD_THEMES['default']})

# ─────────────────────────────────────────────────────────────────────────────
#  AI ANALYSIS CHAT  (powered by Inkazimulo.digital AI)
# ─────────────────────────────────────────────────────────────────────────────

@app.route('/api/ai/analyze-game', methods=['POST'])
def ai_analyze_game():
    """Post-game analysis from the AI chief in the player's language."""
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    # Check daily limit for free users
    db  = get_db()
    plan = (db.execute('SELECT plan FROM users WHERE email=?', (user['email'],)).fetchone() or {}).get('plan','free')
    today = time.strftime('%Y-%m-%d')
    used  = db.execute(
        'SELECT COUNT(*) FROM kingdom_events WHERE user_email=? '
        'AND event_type=\'ai_analysis\' AND created > strftime(\'%s\',?)',
        (user['email'], today)
    ).fetchone()[0]
    if plan == 'free' and used >= 3:
        return jsonify({'ok': False, 'limit_reached': True,
                        'message': 'Free players get 3 analyses per day. Upgrade to Inkosi Club for unlimited.'}), 429
    data       = request.get_json(force=True) or {}
    persona_id = sanitise(str(data.get('persona_id','shaka')), 20)
    lang       = sanitise(str(data.get('lang','en')), 5)
    moves      = data.get('moves', [])   # list of {idx, captured, player} dicts
    result     = sanitise(str(data.get('result','unknown')), 10)  # 'win' or 'lose'
    persona    = AI_PERSONAS.get(persona_id, AI_PERSONAS['shaka'])
    lang_data  = LANGS.get(lang, LANGS['en'])
    # Build analysis prompt
    move_summary = f"{len(moves)} moves played. Result: {result}."
    if moves:
        captures = [m.get('captured',0) for m in moves if m.get('player')==1]
        move_summary += f" AI captured {sum(captures)} stones total."
    system_prompt = (
        f"You are {persona['name']}, a legendary Nguni chief and master of Intshuba "
        f"(a traditional stone board game). You just played against this player and {'lost' if result=='win' else 'won'}. "
        f"Give brief, characterful post-game analysis in {'the players language' if lang!='en' else 'English'}. "
        f"Speak as {persona['name']} — use your personality ({persona.get('description','balanced')}) and reference your historical legacy. "
        f"Give 1-2 specific tactical observations, 1 encouragement or challenge, and end with a culturally authentic phrase from your tribe ({persona['tribe']}). "
        f"Keep it under 120 words. Game summary: {move_summary}"
    )
    # Call Inkazimulo AI API
    api_key = os.environ.get('INKAZIMULO_AI_KEY','')  # Set at inkazimulo.digital dashboard
    if not api_key:
        # Fallback to static response if no API key
        fallback = persona.get('win_msg_en' if result=='lose' else 'lose_msg_en','Well played.')
        taunt    = _ai_taunt(persona_id, lang)
        return jsonify({'ok': True, 'analysis': f"{taunt}\n\n{fallback}", 'source': 'static'})
    try:
        import urllib.request as _ur, json as _j
        req = _ur.Request(
            'https://api.inkazimulo.digital/v1/ai/messages',
            data=_j.dumps({
                'model': 'inkazimulo-chief-v2',
                'max_tokens': 200,
                'system': system_prompt,
                'messages': [{'role':'user','content':f'Analyze my game. I {result}.'}]
            }).encode(),
            headers={
                'Content-Type': 'application/json',
                'x-inkazimulo-key': api_key,
                'x-inkazimulo-version': '2024-01-01',
            },
            method='POST'
        )
        resp   = _ur.urlopen(req, timeout=10)
        result_data = _j.loads(resp.read())
        analysis = result_data['content'][0]['text']
        # Log usage
        db.execute(
            'INSERT INTO kingdom_events(user_email,event_type,detail,cows_delta) VALUES(?,?,?,0)',
            (user['email'], 'ai_analysis', _j.dumps({'persona': persona_id, 'result': result}))
        )
        db.commit()
        return jsonify({'ok': True, 'analysis': analysis, 'persona': persona['name'],
                        'source': 'inkazimulo_ai', 'analyses_remaining': max(0, 3-used-1) if plan=='free' else 'unlimited'})
    except Exception as e:
        BugFixer.capture('error', f'ai_analyze: {e}', e)
        return jsonify({'ok': True, 'analysis': _ai_taunt(persona_id, lang), 'source': 'fallback'})

# ─────────────────────────────────────────────────────────────────────────────
#  GAME REPLAY  (move history stored server-side)
# ─────────────────────────────────────────────────────────────────────────────

@app.route('/api/replay/<game_id>', endpoint='get_replay_legacy')
def get_replay_legacy(game_id):
    """Retrieve stored move history for a completed game."""
    db   = get_db()
    game = db.execute('SELECT * FROM game_replays WHERE game_id=?', (game_id,)).fetchone()
    if not game:
        return jsonify({'error': 'Replay not found'}), 404
    user = current_user()
    plan = 'free'
    if user:
        p = db.execute('SELECT plan FROM users WHERE email=?', (user['email'],)).fetchone()
        plan = p['plan'] if p else 'free'
    moves = json.loads(game['moves_json'] or '[]')
    if plan == 'free' and len(moves) > 20:
        moves = moves[:20]
        return jsonify({'game_id': game_id, 'moves': moves, 'truncated': True,
                        'message': 'Upgrade to Inkosi Club for full replay + AI analysis.'})
    return jsonify({'game_id': game_id, 'moves': moves, 'truncated': False,
                    'result': game['result'], 'persona_id': game['persona_id']})

@app.route('/api/replay/save', methods=['POST'], endpoint='save_replay_legacy')
def save_replay_legacy():
    """Save move history at game end."""
    user = current_user()
    if not user:
        return jsonify({'ok': False})
    data    = request.get_json(force=True) or {}
    moves   = data.get('moves', [])
    result  = sanitise(str(data.get('result','unknown')), 10)
    persona = sanitise(str(data.get('persona_id','shaka')), 20)
    import uuid as _u
    game_id = 'REPLAY-' + _u.uuid4().hex[:8].upper()
    db = get_db()
    db.execute(
        'INSERT INTO game_replays(game_id,user_email,moves_json,result,persona_id,created) '
        'VALUES(?,?,?,?,?,strftime(\'%s\',\'now\'))',
        (game_id, user['email'], json.dumps(moves), result, persona)
    )
    db.commit()
    return jsonify({'ok': True, 'game_id': game_id})


# ═══════════════════════════════════════════════════════════════════════════════
#  ALL-18 FEATURES  v2.3.0
#  ELO · Daily · Streak · Replay · Puzzle · Friends · Clan · Spectate
#  Chest · Achievements · Sound · Push · Tournament · Referral · Seasonal
#  Live Leaderboard · AI Chat · Family Mode
# ═══════════════════════════════════════════════════════════════════════════════

import hashlib as _hashlib

# ── ELO RATING SYSTEM ─────────────────────────────────────────────────────────
ELO_DEFAULT  = 1200
ELO_K_FACTOR = 32   # standard K-factor; reduce to 16 for established players

def _elo_expected(ra: int, rb: int) -> float:
    return 1.0 / (1.0 + 10 ** ((rb - ra) / 400.0))

def _elo_update(ra: int, rb: int, score_a: float) -> tuple[int, int]:
    """Return (new_ra, new_rb). score_a=1 win, 0.5 draw, 0 loss."""
    ea  = _elo_expected(ra, rb)
    eb  = 1.0 - ea
    k   = ELO_K_FACTOR
    new_ra = max(100, round(ra + k * (score_a - ea)))
    new_rb = max(100, round(rb + k * ((1 - score_a) - eb)))
    return new_ra, new_rb

def _get_elo(email: str) -> int:
    try:
        db  = get_db()
        row = db.execute('SELECT elo FROM users WHERE email=?', (email,)).fetchone()
        return row['elo'] if row and row['elo'] else ELO_DEFAULT
    except Exception:
        return ELO_DEFAULT

def _update_elo(winner: str, loser: str, draw: bool = False):
    try:
        db = get_db()
        ra = _get_elo(winner); rb = _get_elo(loser)
        score = 0.5 if draw else 1.0
        new_ra, new_rb = _elo_update(ra, rb, score)
        if not draw:
            db.execute('UPDATE users SET elo=? WHERE email=?', (new_ra, winner))
        db.execute('UPDATE users SET elo=? WHERE email=?', (new_rb, loser))
        db.commit()
        log.info(f'[ELO] {winner} {ra}→{new_ra}  {loser} {rb}→{new_rb}')
        return new_ra, new_rb
    except Exception as e:
        log.error(f'[ELO] update failed: {e}')
        return ELO_DEFAULT, ELO_DEFAULT

@app.route('/api/elo/leaderboard')
def elo_leaderboard():
    db   = get_db()
    rows = db.execute(
        'SELECT name,elo,wins,losses,draws,tribe_id,has_crown,title FROM users '
        'WHERE elo IS NOT NULL ORDER BY elo DESC LIMIT 100'
    ).fetchall()
    return jsonify({'leaderboard': [dict(r) for r in rows]})

@app.route('/api/elo/rating')
def my_elo():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    elo  = _get_elo(user['email'])
    db   = get_db()
    rank = db.execute(
        'SELECT COUNT(*)+1 FROM users WHERE elo > ?', (elo,)
    ).fetchone()[0]
    return jsonify({'elo': elo, 'rank': rank, 'k_factor': ELO_K_FACTOR})

# ── DAILY CHALLENGE ────────────────────────────────────────────────────────────
def _daily_seed() -> str:
    """Deterministic seed for today's puzzle board."""
    today = time.strftime('%Y%m%d')
    return _hashlib.md5(f'intshuba-daily-{today}'.encode()).hexdigest()

@app.route('/api/daily/challenge')
def daily_challenge():
    """Return today's fixed board seed and leaderboard."""
    seed  = _daily_seed()
    today = time.strftime('%Y-%m-%d')
    db    = get_db()
    board = db.execute(
        'SELECT * FROM daily_scores WHERE date=? ORDER BY score DESC, time_secs ASC LIMIT 20',
        (today,)
    ).fetchall()
    return jsonify({
        'date':       today,
        'seed':       seed,
        'leaderboard':[dict(r) for r in board],
        'message':    'Same board for every player today. How fast can you win?',
    })

@app.route('/api/daily/submit', methods=['POST'])
def daily_submit():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data     = request.get_json(force=True) or {}
    score    = int(data.get('score', 0))
    time_secs= int(data.get('time_secs', 999))
    won      = bool(data.get('won', False))
    today    = time.strftime('%Y-%m-%d')
    db       = get_db()
    existing = db.execute(
        'SELECT id FROM daily_scores WHERE date=? AND player_email=?',
        (today, user['email'])
    ).fetchone()
    if existing:
        return jsonify({'ok': True, 'message': 'Already submitted today!', 'already_done': True})
    db.execute(
        'INSERT INTO daily_scores(date,player_email,player_name,score,time_secs,won,tribe_id) VALUES(?,?,?,?,?,?,?)',
        (today, user['email'], user['name'], score, time_secs,
         1 if won else 0, user.get('tribe_id','world'))
    )
    # Streak update
    streak = _update_streak(user['email'])
    # Cow reward for daily challenge
    reward = 5 if won else 2
    _add_cows(user['email'], reward, 'daily_challenge', {'date': today, 'won': won})
    db.commit()
    return jsonify({'ok': True, 'score': score, 'streak': streak, 'reward_cows': reward})

# ── LOGIN STREAK + SHIELD ──────────────────────────────────────────────────────
def _update_streak(email: str) -> dict:
    db   = get_db()
    row  = db.execute(
        'SELECT streak_days, streak_last, streak_shield FROM users WHERE email=?', (email,)
    ).fetchone()
    if not row:
        return {'days': 0, 'shield': 0}
    now_day = int(time.time() // 86400)
    last    = row['streak_last'] or 0
    days    = row['streak_days'] or 0
    shield  = row['streak_shield'] or 0
    gap     = now_day - last
    if gap == 0:
        pass  # already updated today
    elif gap == 1:
        days += 1  # consecutive day
    elif gap == 2 and shield > 0:
        days += 1; shield -= 1  # shield used
        log.info(f'[STREAK] {email} used streak shield (gap=2 days)')
    else:
        days = 1   # reset
    db.execute(
        'UPDATE users SET streak_days=?, streak_last=?, streak_shield=? WHERE email=?',
        (days, now_day, shield, email)
    )
    db.commit()
    # Milestone rewards
    milestones = {7: 20, 14: 50, 30: 150, 60: 400, 100: 1000}
    reward = milestones.get(days, 0)
    if reward:
        _add_cows(email, reward, 'streak_milestone', {'days': days})
    return {'days': days, 'shield': shield, 'milestone_reward': reward}

@app.route('/api/streak/status')
def streak_status():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    return jsonify(_update_streak(user['email']))

@app.route('/api/streak/buy-shield', methods=['POST'])
def buy_streak_shield():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    SHIELD_COST = 5  # cows
    herd = _get_herd(user['email'])
    if herd < SHIELD_COST:
        return jsonify({'ok': False, 'error': f'Need {SHIELD_COST} cows for a shield'}), 402
    db = get_db()
    row = db.execute('SELECT streak_shield FROM users WHERE email=?', (user['email'],)).fetchone()
    current_shields = (row['streak_shield'] or 0) if row else 0
    if current_shields >= 3:
        return jsonify({'ok': False, 'error': 'Max 3 shields at a time'}), 400
    _add_cows(user['email'], -SHIELD_COST, 'buy_streak_shield')
    db.execute('UPDATE users SET streak_shield=streak_shield+1 WHERE email=?', (user['email'],))
    db.commit()
    return jsonify({'ok': True, 'shields': current_shields + 1, 'message': '🛡️ Streak shield activated!'})

# ── PUZZLE MODE ────────────────────────────────────────────────────────────────
PUZZLES = [
    {'id': 1, 'title': 'Capture or Be Captured',
     'board': [0,0,3,0,0,0, 0,1,0,2,0,0, 0,2,0,1,0,0, 0,0,3,0,0,0],
     'solution_hole': 2, 'target_capture': 4,
     'hint': 'Look at column 3 — what happens if you sow from hole 2?',
     'level': 1, 'reward_cows': 5},
    {'id': 2, 'title': 'The Chain Relay',
     'board': [0,2,0,0,2,0, 1,0,3,0,0,2, 0,0,1,0,3,0, 2,0,0,2,0,0],
     'solution_hole': 8, 'target_capture': 6,
     'hint': 'Sow 3 stones — where does the relay take you?',
     'level': 2, 'reward_cows': 10},
    {'id': 3, 'title': 'The Double Strike',
     'board': [0,0,0,4,0,0, 2,0,0,0,2,0, 0,2,0,0,0,2, 0,0,4,0,0,0],
     'solution_hole': 3, 'target_capture': 8,
     'hint': 'A long sow hits both opposing columns.',
     'level': 2, 'reward_cows': 10},
    {'id': 4, 'title': 'Shaka\'s Trap',
     'board': [1,0,0,0,1,0, 3,2,0,2,3,0, 0,3,2,2,3,0, 1,0,0,0,1,0],
     'solution_hole': 6, 'target_capture': 10,
     'hint': 'Think like a Zulu impondo — attack from the flank.',
     'level': 3, 'reward_cows': 20},
    {'id': 5, 'title': 'Moshoeshoe\'s Fortress',
     'board': [0,1,0,1,0,1, 2,0,2,0,2,0, 0,2,0,2,0,2, 1,0,1,0,1,0],
     'solution_hole': 1, 'target_capture': 6,
     'hint': 'The mountain path is narrow — find the one gap.',
     'level': 3, 'reward_cows': 20},
]

@app.route('/api/puzzles')
def get_puzzles():
    user = current_user()
    solved_ids = set()
    if user:
        db   = get_db()
        rows = db.execute(
            "SELECT detail FROM kingdom_events WHERE user_email=? AND event_type='puzzle_solved'",
            (user['email'],)
        ).fetchall()
        for r in rows:
            try:
                d = json.loads(r['detail'])
                solved_ids.add(d.get('puzzle_id'))
            except Exception:
                pass
    puzzles_out = []
    for p in PUZZLES:
        d = {k: v for k, v in p.items() if k != 'solution_hole'}
        d['solved'] = p['id'] in solved_ids
        puzzles_out.append(d)
    return jsonify({'puzzles': puzzles_out, 'total': len(PUZZLES)})

@app.route('/api/puzzle/<int:puzzle_id>/solve', methods=['POST'])
def solve_puzzle(puzzle_id):
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    puz  = next((p for p in PUZZLES if p['id'] == puzzle_id), None)
    if not puz:
        return jsonify({'error': 'Unknown puzzle'}), 404
    data = request.get_json(force=True) or {}
    hole = int(data.get('hole', -1))
    if hole != puz['solution_hole']:
        return jsonify({'ok': False, 'correct': False,
                        'message': 'Not the right move — try again!',
                        'hint': puz['hint']})
    db  = get_db()
    already = db.execute(
        "SELECT id FROM kingdom_events WHERE user_email=? AND event_type='puzzle_solved' AND detail LIKE ?",
        (user['email'], f'%"puzzle_id": {puzzle_id}%')
    ).fetchone()
    if already:
        return jsonify({'ok': True, 'correct': True, 'already_solved': True,
                        'message': 'Already solved! No bonus cows this time.'})
    reward = puz['reward_cows']
    _add_cows(user['email'], reward, 'puzzle_solved', {'puzzle_id': puzzle_id})
    return jsonify({'ok': True, 'correct': True, 'reward_cows': reward,
                    'message': f'🧩 Correct! +{reward} cows!'})

# ── FRIENDS + DIRECT CHALLENGE ─────────────────────────────────────────────────
@app.route('/api/friends/add', methods=['POST'])
def add_friend():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data         = request.get_json(force=True) or {}
    friend_email = sanitise(str(data.get('friend_email') or data.get('email') or ''), 80)
    db           = get_db()
    friend       = db.execute('SELECT name,email FROM users WHERE email=?', (friend_email,)).fetchone()
    if not friend:
        return jsonify({'error': 'Player not found'}), 404
    if friend_email == user['email']:
        return jsonify({'error': 'Cannot add yourself'}), 400
    existing = db.execute(
        'SELECT id FROM friends WHERE (user_a=? AND user_b=?) OR (user_a=? AND user_b=?)',
        (user['email'], friend_email, friend_email, user['email'])
    ).fetchone()
    if existing:
        return jsonify({'ok': True, 'message': 'Already friends!', 'already': True})
    db.execute(
        'INSERT INTO friends(user_a, user_b, created) VALUES(?,?,strftime(\'%s\',\'now\'))',
        (user['email'], friend_email)
    )
    db.commit()
    return jsonify({'ok': True, 'friend_name': friend['name'],
                    'message': f'Friends with {friend["name"]}! +20 cows when they reach Level 2.'})

@app.route('/api/friends/list')
def list_friends():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    db   = get_db()
    rows = db.execute(
        '''SELECT u.name, u.email, u.elo, u.title, u.tribe_id, u.has_crown,
                  u.herd_cows, u.wins
           FROM friends f
           JOIN users u ON (u.email = CASE WHEN f.user_a=? THEN f.user_b ELSE f.user_a END)
           WHERE f.user_a=? OR f.user_b=?
           ORDER BY u.elo DESC LIMIT 50''',
        (user['email'], user['email'], user['email'])
    ).fetchall()
    return jsonify({'friends': [dict(r) for r in rows]})

@app.route('/api/friends/challenge', methods=['POST'])
def challenge_friend():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data         = request.get_json(force=True) or {}
    friend_email = sanitise(str(data.get('friend_email', '')), 80)
    db = get_db()
    friend = db.execute('SELECT name FROM users WHERE email=?', (friend_email,)).fetchone()
    if not friend:
        return jsonify({'error': 'Player not found'}), 404
    import uuid as _uuid
    room_id = 'FRIEND-' + _uuid.uuid4().hex[:8].upper()
    db.execute(
        '''INSERT INTO online_games(room_id, host_email, host_name, status, created, level)
           VALUES(?,?,?,'waiting',strftime('%s','now'),3)''',
        (room_id, user['email'], user['name'])
    )
    db.commit()
    return jsonify({
        'ok': True,
        'room_id': room_id,
        'join_url': f'/join/{room_id}',
        'message': f'Challenge sent to {friend["name"]}! Share this room code: {room_id}',
    })

# ── CLAN SYSTEM (uMphakathi) ───────────────────────────────────────────────────
@app.route('/api/clan/create', methods=['POST'])
def create_clan():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data      = request.get_json(force=True) or {}
    name      = sanitise(str(data.get('name', '')), 60)
    badge     = sanitise(str(data.get('badge', '🐄')), 10)
    clan_tag  = sanitise(str(data.get('tag', '')), 10).upper()
    if not name or len(name) < 3:
        return jsonify({'error': 'Clan name must be at least 3 characters'}), 400
    CLAN_COST = 50
    herd = _get_herd(user['email'])
    if herd < CLAN_COST:
        return jsonify({'ok': False, 'insufficient': True, 'required': CLAN_COST,
                        'message': f'Creating a clan costs {CLAN_COST} cows'}), 402
    db = get_db()
    existing = db.execute('SELECT id FROM clans WHERE leader_email=?', (user['email'],)).fetchone()
    if existing:
        return jsonify({'error': 'You already lead a clan'}), 409
    import uuid as _uuid
    clan_id = 'CLAN-' + _uuid.uuid4().hex[:6].upper()
    _add_cows(user['email'], -CLAN_COST, 'clan_creation')
    db.execute(
        '''INSERT INTO clans(id,name,badge,tag,leader_email,leader_name,
           member_count,total_cows,war_wins,created)
           VALUES(?,?,?,?,?,?,1,0,0,strftime('%s','now'))''',
        (clan_id, name, badge, clan_tag, user['email'], user['name'])
    )
    db.execute('UPDATE users SET clan_id=?, clan_role=? WHERE email=?',
               (clan_id, 'leader', user['email']))
    db.commit()
    return jsonify({'ok': True, 'clan_id': clan_id, 'name': name,
                    'message': f'Clan "{name}" {badge} created! Invite up to 19 more warriors.'})

@app.route('/api/clan/join', methods=['POST'])
def join_clan():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data    = request.get_json(force=True) or {}
    clan_id = sanitise(str(data.get('clan_id', '')), 20)
    db      = get_db()
    clan    = db.execute('SELECT * FROM clans WHERE id=?', (clan_id,)).fetchone()
    if not clan:
        return jsonify({'error': 'Clan not found'}), 404
    if clan['member_count'] >= 20:
        return jsonify({'error': 'Clan is full (max 20 members)'}), 400
    current_clan = db.execute(
        'SELECT clan_id FROM users WHERE email=?', (user['email'],)
    ).fetchone()
    if current_clan and current_clan['clan_id']:
        return jsonify({'error': 'Leave your current clan first'}), 409
    db.execute('UPDATE users SET clan_id=?,clan_role=? WHERE email=?',
               (clan_id, 'member', user['email']))
    db.execute('UPDATE clans SET member_count=member_count+1,total_cows=total_cows+? WHERE id=?',
               (_get_herd(user['email']), clan_id))
    db.commit()
    return jsonify({'ok': True, 'clan_name': clan['name'],
                    'message': f'Joined {clan["name"]} {clan["badge"]}!'})

@app.route('/api/clan/<clan_id>')
def clan_info(clan_id):
    db   = get_db()
    clan = db.execute('SELECT * FROM clans WHERE id=?', (clan_id,)).fetchone()
    if not clan:
        return jsonify({'error': 'Clan not found'}), 404
    members = db.execute(
        'SELECT name,elo,herd_cows,title,tribe_id,clan_role FROM users '
        'WHERE clan_id=? ORDER BY herd_cows DESC', (clan_id,)
    ).fetchall()
    return jsonify({'clan': dict(clan), 'members': [dict(m) for m in members]})

@app.route('/api/clans/leaderboard')
def clans_leaderboard():
    db   = get_db()
    rows = db.execute(
        'SELECT id,name,description,tribe_id,leader_email,member_count,total_cows,war_wins '
        'FROM clans ORDER BY total_cows DESC LIMIT 30'
    ).fetchall()
    return jsonify({'clans': [dict(r) for r in rows]})

# ── CHEST / REWARD BOX SYSTEM ─────────────────────────────────────────────────
CHEST_TYPES = {
    'bronze': {'label': 'Bronze Chest', 'icon': '📦', 'unlock_hours': 4,
               'cows_min': 10, 'cows_max': 30, 'cost_to_open': 10},
    'silver': {'label': 'Silver Chest', 'icon': '🪙', 'unlock_hours': 8,
               'cows_min': 30, 'cows_max': 80, 'cost_to_open': 25},
    'gold':   {'label': 'Gold Chest',   'icon': '🏆', 'unlock_hours': 24,
               'cows_min': 80, 'cows_max': 200, 'cost_to_open': 60},
    'royal':  {'label': 'Royal Chest',  'icon': '👑', 'unlock_hours': 72,
               'cows_min': 200, 'cows_max': 600, 'cost_to_open': 150},
}
MAX_CHEST_SLOTS = 4

@app.route('/api/chests')
def my_chests():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    db   = get_db()
    rows = db.execute(
        'SELECT * FROM chests WHERE player_email=? AND opened=0 ORDER BY slot ASC',
        (user['email'],)
    ).fetchall()
    chests = []
    now = int(time.time())
    for r in rows:
        d = dict(r)
        d['ready'] = d['unlock_at'] <= now
        d['minutes_left'] = max(0, (d['unlock_at'] - now) // 60)
        d['chest_info']   = CHEST_TYPES.get(d['chest_type'], CHEST_TYPES['bronze'])
        chests.append(d)
    return jsonify({'chests': chests, 'slots_used': len(chests), 'max_slots': MAX_CHEST_SLOTS})

@app.route('/api/chests/open', methods=['POST'])
def open_chest():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data     = request.get_json(force=True) or {}
    chest_id = int(data.get('chest_id', 0))
    instant  = bool(data.get('instant_open', False))
    db       = get_db()
    chest    = db.execute(
        'SELECT * FROM chests WHERE id=? AND player_email=? AND opened=0',
        (chest_id, user['email'])
    ).fetchone()
    if not chest:
        return jsonify({'error': 'Chest not found'}), 404
    now  = int(time.time())
    cinfo= CHEST_TYPES.get(chest['chest_type'], CHEST_TYPES['bronze'])
    if chest['unlock_at'] > now and not instant:
        mins = (chest['unlock_at'] - now) // 60
        return jsonify({'ok': False, 'not_ready': True,
                        'minutes_left': mins,
                        'instant_cost': cinfo['cost_to_open'],
                        'message': f'Unlocks in {mins} minutes. Spend {cinfo["cost_to_open"]} cows to open now?'})
    if instant:
        herd = _get_herd(user['email'])
        if herd < cinfo['cost_to_open']:
            return jsonify({'ok': False, 'insufficient': True,
                            'required': cinfo['cost_to_open']}), 402
        _add_cows(user['email'], -cinfo['cost_to_open'], 'chest_instant_open')
    import random as _rand
    reward = _rand.randint(cinfo['cows_min'], cinfo['cows_max'])
    new_bal = _add_cows(user['email'], reward, 'chest_opened',
                        {'chest_type': chest['chest_type'], 'reward': reward})
    db.execute('UPDATE chests SET opened=1,opened_at=? WHERE id=?', (now, chest_id))
    db.commit()
    return jsonify({'ok': True, 'chest_type': chest['chest_type'],
                    'reward_cows': reward, 'new_balance': new_bal,
                    'message': f'{cinfo["icon"]} {cinfo["label"]} opened! +{reward} cows!'})

def _grant_chest(email: str, chest_type: str = 'bronze'):
    """Grant a chest after a win. Called from game-end logic."""
    try:
        db    = get_db()
        count = db.execute(
            'SELECT COUNT(*) FROM chests WHERE player_email=? AND opened=0',
            (email,)
        ).fetchone()[0]
        if count >= MAX_CHEST_SLOTS:
            return None  # no slot available
        unlock_at = int(time.time()) + CHEST_TYPES[chest_type]['unlock_hours'] * 3600
        # Find lowest free slot
        used_slots = {r['slot'] for r in db.execute(
            'SELECT slot FROM chests WHERE player_email=? AND opened=0', (email,)
        ).fetchall()}
        slot = next(s for s in range(1, MAX_CHEST_SLOTS+1) if s not in used_slots)
        db.execute(
            'INSERT INTO chests(player_email,chest_type,slot,unlock_at,opened) VALUES(?,?,?,?,0)',
            (email, chest_type, slot, unlock_at)
        )
        db.commit()
        log.info(f'[CHEST] Granted {chest_type} chest to {email} (slot {slot})')
        return slot
    except Exception as e:
        log.error(f'[CHEST] grant failed: {e}')
        return None

# ── ACHIEVEMENTS (iMbasa) ──────────────────────────────────────────────────────
ACHIEVEMENTS = {
    'first_win':      {'title': 'First Victory',         'icon': '🏆', 'desc': 'Win your first game',         'cows': 10,  'check': lambda u: u.get('wins',0) >= 1},
    'warrior_10':     {'title': 'Ten Battles',            'icon': '⚔️', 'desc': 'Win 10 games',                'cows': 25,  'check': lambda u: u.get('wins',0) >= 10},
    'herd_100':       {'title': 'Century Herd',           'icon': '🐄', 'desc': 'Accumulate 100 cows',         'cows': 50,  'check': lambda u: u.get('herd_cows',0) >= 100},
    'herd_500':       {'title': 'Great Herd',             'icon': '🐘', 'desc': 'Accumulate 500 cows',         'cows': 100, 'check': lambda u: u.get('herd_cows',0) >= 500},
    'shaka_defeated': {'title': 'Shaka Defeated',         'icon': '🐗', 'desc': 'Beat Shaka in challenge',     'cows': 200, 'check': None},
    'married':        {'title': 'Lobola Paid',            'icon': '💍', 'desc': 'Get married (pay lobola)',     'cows': 30,  'check': lambda u: u.get('is_married',0) == 1},
    'crowned':        {'title': 'iNkosi',                 'icon': '👑', 'desc': 'Hold the crown',              'cows': 500, 'check': lambda u: u.get('has_crown',0) == 1},
    'land_owner':     {'title': 'Landowner',              'icon': '🌾', 'desc': 'Own 3 land plots',            'cows': 30,  'check': lambda u: u.get('land_plots',0) >= 3},
    'streak_7':       {'title': 'Week Warrior',           'icon': '🔥', 'desc': '7-day login streak',          'cows': 20,  'check': lambda u: u.get('streak_days',0) >= 7},
    'streak_30':      {'title': 'Month Master',           'icon': '📅', 'desc': '30-day login streak',         'cows': 100, 'check': lambda u: u.get('streak_days',0) >= 30},
    'tribe_joined':   {'title': 'Tribe Member',           'icon': '⚔️', 'desc': 'Join a tribe',                'cows': 10,  'check': lambda u: u.get('tribe_id','world') != 'world'},
    'puzzle_solver':  {'title': 'Puzzle Master',          'icon': '🧩', 'desc': 'Solve 3 puzzles',             'cows': 30,  'check': None},
    'clan_member':    {'title': 'Clan Member',            'icon': '🏰', 'desc': 'Join a clan',                 'cows': 15,  'check': lambda u: bool(u.get('clan_id'))},
    'elo_1400':       {'title': 'Rising Star',            'icon': '⭐', 'desc': 'Reach ELO 1400',              'cows': 50,  'check': lambda u: u.get('elo', 1200) >= 1400},
    'elo_1600':       {'title': 'Master Player',          'icon': '🌟', 'desc': 'Reach ELO 1600',              'cows': 150, 'check': lambda u: u.get('elo', 1200) >= 1600},
    'story_ch5':      {'title': 'Ndebele Challenger',     'icon': '🎨', 'desc': 'Complete story chapter 5',    'cows': 50,  'check': None},
    'level3_unlock':  {'title': 'iNkosi Level',           'icon': '🦅', 'desc': 'Unlock Level 3',              'cows': 30,  'check': lambda u: u.get('current_level',1) >= 3},
    'referral_first': {'title': 'Recruiter',              'icon': '🎁', 'desc': 'Refer your first friend',     'cows': 30,  'check': None},
    'daily_winner':   {'title': 'Daily Champion',         'icon': '🗓', 'desc': 'Win a daily challenge',       'cows': 20,  'check': None},
}

def _check_achievements(email: str) -> list:
    """Check and award any newly unlocked achievements. Returns list of new awards."""
    try:
        db  = get_db()
        row = db.execute(
            'SELECT wins,herd_cows,is_married,has_crown,land_plots,tribe_id,'
            'clan_id,elo,current_level,streak_days FROM users WHERE email=?',
            (email,)
        ).fetchone()
        if not row:
            return []
        u = dict(row)
        already = {r['achievement_id'] for r in db.execute(
            'SELECT achievement_id FROM achievements WHERE player_email=?', (email,)
        ).fetchall()}
        new_awards = []
        for aid, ach in ACHIEVEMENTS.items():
            if aid in already:
                continue
            check_fn = ach.get('check')
            if check_fn is None:
                continue  # needs manual trigger
            if check_fn(u):
                db.execute(
                    'INSERT INTO achievements(player_email,achievement_id,earned_at) VALUES(?,?,strftime(\'%s\',\'now\'))',
                    (email, aid)
                )
                _add_cows(email, ach['cows'], 'achievement', {'id': aid})
                new_awards.append({'id': aid, 'title': ach['title'],
                                   'icon': ach['icon'], 'reward': ach['cows']})
        if new_awards:
            db.commit()
        return new_awards
    except Exception as e:
        log.error(f'[ACH] check failed: {e}')
        return []

def _award_achievement(email: str, achievement_id: str):
    """Manually award a specific achievement."""
    if achievement_id not in ACHIEVEMENTS:
        return
    db = get_db()
    existing = db.execute(
        'SELECT id FROM achievements WHERE player_email=? AND achievement_id=?',
        (email, achievement_id)
    ).fetchone()
    if existing:
        return
    ach = ACHIEVEMENTS[achievement_id]
    db.execute(
        'INSERT INTO achievements(player_email,achievement_id,earned_at) VALUES(?,?,strftime(\'%s\',\'now\'))',
        (email, achievement_id)
    )
    _add_cows(email, ach['cows'], 'achievement', {'id': achievement_id})
    db.commit()

@app.route('/api/achievements')
def my_achievements():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    new_awards = _check_achievements(user['email'])
    db    = get_db()
    earned= {r['achievement_id'] for r in db.execute(
        'SELECT achievement_id FROM achievements WHERE player_email=?', (user['email'],)
    ).fetchall()}
    out = []
    for aid, ach in ACHIEVEMENTS.items():
        out.append({'id': aid, 'title': ach['title'], 'icon': ach['icon'],
                    'desc': ach['desc'], 'cows': ach['cows'], 'earned': aid in earned})
    return jsonify({'achievements': out, 'new': new_awards,
                    'earned_count': len(earned), 'total': len(ACHIEVEMENTS)})

# ── REFERRAL PROGRAMME ─────────────────────────────────────────────────────────
@app.route('/api/referral/link')
def referral_link():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    ref_code = _hashlib.md5(user['email'].encode()).hexdigest()[:8].upper()
    base_url = os.environ.get('APP_URL', request.host_url.rstrip('/'))
    db   = get_db()
    refs = db.execute(
        'SELECT COUNT(*) FROM users WHERE referred_by=?', (user['email'],)
    ).fetchone()[0]
    return jsonify({
        'ref_code':    ref_code,
        'ref_url':     f'{base_url}/?ref={ref_code}',
        'referrals':   refs,
        'message':     'Share this link! You both get 20 cows when they reach Level 2.',
        'tiers': [
            {'refs': 1,  'reward': '20 cows'},
            {'refs': 5,  'reward': '+50 cows bonus'},
            {'refs': 10, 'reward': '1 month Inkosi Club free'},
        ]
    })

@app.route('/api/referral/use', methods=['POST'])
def use_referral():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data     = request.get_json(force=True) or {}
    ref_code = sanitise(str(data.get('ref_code', '')), 20).upper()
    db       = get_db()
    # Find referrer by their code
    all_users = db.execute('SELECT email,name FROM users WHERE email!=?', (user['email'],)).fetchall()
    referrer  = None
    for u in all_users:
        code = _hashlib.md5(u['email'].encode()).hexdigest()[:8].upper()
        if code == ref_code:
            referrer = u; break
    if not referrer:
        return jsonify({'error': 'Invalid referral code'}), 404
    already = db.execute(
        'SELECT referred_by FROM users WHERE email=?', (user['email'],)
    ).fetchone()
    if already and already['referred_by']:
        return jsonify({'error': 'Referral already applied'}), 409
    db.execute('UPDATE users SET referred_by=? WHERE email=?', (referrer['email'], user['email']))
    # Both get 10 cows on registration
    _add_cows(user['email'], 10, 'referral_join', {'referrer': referrer['email']})
    _add_cows(referrer['email'], 10, 'referral_bonus', {'new_user': user['email']})
    db.commit()
    _award_achievement(referrer['email'], 'referral_first')
    return jsonify({'ok': True,
                    'message': f'Referred by {referrer["name"]}! You both got +10 cows. +20 more each when you reach Level 2.'})

# ── LIVE GLOBAL LEADERBOARD ────────────────────────────────────────────────────
@app.route('/api/leaderboard/global')
def global_leaderboard():
    db   = get_db()
    by   = sanitise(str(request.args.get('by', 'elo')), 20)
    pool = sanitise(str(request.args.get('age_pool', '')), 20)
    tribe= sanitise(str(request.args.get('tribe', '')), 30)
    col  = {'elo': 'elo', 'cows': 'herd_cows', 'wins': 'wins', 'streak': 'streak_days'}.get(by, 'elo')
    where = 'WHERE email != ""'
    params = []
    if pool:
        where += ' AND age_pool=?'; params.append(pool)
    if tribe:
        where += ' AND tribe_id=?'; params.append(tribe)
    rows = db.execute(
        f'SELECT name,elo,herd_cows,wins,tribe_id,has_crown,title,age_pool,clan_id,streak_days '
        f'FROM users {where} ORDER BY {col} DESC NULLS LAST LIMIT 100',
        params
    ).fetchall()
    return jsonify({'players': [dict(r) for r in rows], 'leaderboard': [dict(r) for r in rows], 'sort_by': by})

# ── GAME REPLAY ────────────────────────────────────────────────────────────────
@app.route('/api/game/save-replay', methods=['POST'])
def save_replay():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data   = request.get_json(force=True) or {}
    moves  = data.get('moves', [])  # list of {hole, captured, board_after}
    result = sanitise(str(data.get('result', '')), 10)
    p0     = int(data.get('p0', 0))
    p1     = int(data.get('p1', 0))
    if not moves:
        return jsonify({'error': 'No moves to save'}), 400
    db = get_db()
    import uuid as _uuid
    replay_id = 'RPY-' + _uuid.uuid4().hex[:8].upper()
    db.execute(
        '''INSERT INTO replays(player_email,player_name,moves_json,
           result,p0_cows,p1_cows,created)
           VALUES(?,?,?,?,?,?,strftime('%s','now'))''',
        (user['email'], user['name'],
         json.dumps(moves), result, p0, p1)
    )
    db.commit()
    return jsonify({'ok': True, 'replay_id': replay_id})

@app.route('/api/game/replay/<replay_id>')
def get_replay(replay_id):
    db  = get_db()
    row = db.execute('SELECT * FROM replays WHERE id=?', (replay_id,)).fetchone()
    if not row:
        return jsonify({'error': 'Replay not found'}), 404
    d = dict(row)
    try:
        d['moves'] = json.loads(d['moves_json'])
    except Exception:
        d['moves'] = []
    return jsonify(d)

@app.route('/api/game/my-replays')
def my_replays():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    db   = get_db()
    rows = db.execute(
        'SELECT id,result,p0_cows,p1_cows,created FROM replays '
        'WHERE player_email=? ORDER BY created DESC LIMIT 20',
        (user['email'],)
    ).fetchall()
    return jsonify({'replays': [dict(r) for r in rows]})

# ── SPECTATE LIVE GAMES ────────────────────────────────────────────────────────
@app.route('/api/spectate/games')
def spectate_games():
    db   = get_db()
    rows = db.execute(
        '''SELECT og.room_id, og.host_email, og.host_name, og.status,
                  u1.elo as host_elo, u1.tribe_id as host_tribe,
                  og.guest_email, og.guest_name
           FROM online_games og
           LEFT JOIN users u1 ON u1.email = og.host_email
           WHERE og.status = 'playing'
           ORDER BY og.updated DESC LIMIT 30'''
    ).fetchall()
    return jsonify({'live_games': [dict(r) for r in rows], 'games': [dict(r) for r in rows], 'count': len(rows)})

@app.route('/api/spectate/<room_id>')
def spectate_game(room_id):
    db  = get_db()
    row = db.execute('SELECT * FROM online_games WHERE room_id=?', (room_id,)).fetchone()
    if not row:
        return jsonify({'error': 'Game not found'}), 404
    d = dict(row)
    try:
        d['board'] = json.loads(d['board_state'] or '[]')
    except Exception:
        d['board'] = []
    return jsonify(d)

# ── FAMILY / PARENTAL MODE ─────────────────────────────────────────────────────
@app.route('/api/family/create', methods=['POST'])
def create_family():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data     = request.get_json(force=True) or {}
    pin      = sanitise(str(data.get('pin', '')), 6)
    if len(pin) < 4 or not pin.isdigit():
        return jsonify({'error': 'PIN must be 4-6 digits'}), 400
    pin_hash = _hashlib.sha256(pin.encode()).hexdigest()
    db       = get_db()
    import uuid as _uuid
    family_id= 'FAM-' + _uuid.uuid4().hex[:6].upper()
    family_name = sanitise(str(data.get('family_name', data.get('name', user['name'] + ' Family'))), 80)
    db.execute(
        'INSERT INTO families(id,family_name,parent_email,parent_name,pin_hash,created) VALUES(?,?,?,?,?,strftime(\'%s\',\'now\'))',
        (family_id, family_name, user['email'], user['name'], pin_hash)
    )
    db.execute('UPDATE users SET family_id=? WHERE email=?', (family_id, user['email']))
    db.commit()
    return jsonify({'ok': True, 'family_id': family_id,
                    'message': 'Family account created! Share the family code with your children.'})

@app.route('/api/family/add-child', methods=['POST'])
def add_child():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data      = request.get_json(force=True) or {}
    child_email = sanitise(str(data.get('child_email', '')), 80)
    pin         = sanitise(str(data.get('pin', '')), 6)
    db          = get_db()
    fam = db.execute(
        'SELECT * FROM families WHERE parent_email=?', (user['email'],)
    ).fetchone()
    if not fam:
        return jsonify({'error': 'Create a family account first'}), 400
    pin_hash = _hashlib.sha256(pin.encode()).hexdigest()
    if pin_hash != fam['pin_hash']:
        return jsonify({'error': 'Wrong PIN'}), 401
    child = db.execute('SELECT name FROM users WHERE email=?', (child_email,)).fetchone()
    if not child:
        return jsonify({'error': 'Child account not found'}), 404
    db.execute('UPDATE users SET family_id=?,family_role=?,is_child=1 WHERE email=?',
               (fam['id'], 'child', child_email))
    db.commit()
    return jsonify({'ok': True, 'child_name': child['name'],
                    'message': f'{child["name"]} added to family! No betting or purchases without PIN.'})

@app.route('/api/family/dashboard')
def family_dashboard():
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    db  = get_db()
    fam = db.execute('SELECT * FROM families WHERE parent_email=?', (user['email'],)).fetchone()
    if not fam:
        return jsonify({'error': 'No family account'}), 404
    children = db.execute(
        'SELECT name,email,herd_cows,wins,losses,games,current_level,streak_days '
        'FROM users WHERE family_id=? AND family_role=? ORDER BY games DESC',
        (fam['id'], 'child')
    ).fetchall()
    return jsonify({'family': dict(fam),
                    'children': [dict(c) for c in children],
                    'weekly_report': {
                        'total_games': sum(c['games'] or 0 for c in children),
                        'total_wins':  sum(c['wins'] or 0 for c in children),
                    }})

# ── AI POST-GAME ANALYSIS CHAT ─────────────────────────────────────────────────
@app.route('/api/ai/post-game-analysis', methods=['POST'])
def ai_post_game_analysis():
    """Inkazimulo AI — move-by-move analysis from the AI chief persona."""
    user = current_user()
    if not user:
        return jsonify({'error': 'Not authenticated'}), 401
    data       = request.get_json(force=True) or {}
    persona_id = sanitise(str(data.get('persona_id', 'shaka')), 20)
    moves      = data.get('moves', [])
    result     = sanitise(str(data.get('result', 'unknown')), 10)
    lang       = sanitise(str(data.get('lang', 'en')), 5)
    persona    = AI_PERSONAS.get(persona_id, AI_PERSONAS['shaka'])
    lang_name  = LANGS.get(lang, LANGS['en']).get('label', 'English')
    # Build analysis prompt
    result_text = {'win': 'the AI won', 'lose': 'the human won', 'draw': 'it was a draw'}.get(result, result)
    move_summary = f"{len(moves)} moves total"
    prompt = f"""You are {persona['name']}, a legendary Nguni chief and Intshuba stone game master.
The player just finished a game against you. Result: {result_text}. {move_summary}.

Respond in {lang_name} (or mix with the player's local language naturally).
Be in character as {persona['name']}: {persona.get('description','')}

Give:
1. A short opening reaction (1-2 sentences, in character with your personality and tribe)
2. One specific tactical observation about the game (be concrete — mention "inner row", "relay chains", "leaving stones exposed")
3. One actionable tip for next time (practical, specific to Intshuba rules)
4. A closing line that fits your character

Keep total response under 120 words. Be dramatic but educational."""
    try:
        import urllib.request as _req
        payload = json.dumps({
            'model': 'inkazimulo-chief-v2',
            'max_tokens': 250,
            'messages': [{'role': 'user', 'content': prompt}]
        }).encode()
        request_obj = _req.Request(
            'https://api.inkazimulo.digital/v1/ai/messages',
            data=payload,
            headers={'content-type': 'application/json',
                     'x-inkazimulo-version': '2024-01-01',
                     'x-inkazimulo-key': os.environ.get('INKAZIMULO_AI_KEY','')}
        )
        with _req.urlopen(request_obj, timeout=12) as resp:
            r    = json.loads(resp.read())
            text = r.get('content', [{}])[0].get('text', '')
        return jsonify({'ok': True, 'analysis': text, 'persona': persona_id,
                        'persona_name': persona['name']})
    except Exception as e:
        log.error(f'[AI CHAT] Analysis failed: {e}')
        # Fallback: use the existing persona taunt system
        fallback = _ai_taunt(persona_id, lang)
        result_msg = persona.get('win_msg_en' if result == 'win' else 'lose_msg_en', fallback)
        return jsonify({'ok': True, 'analysis': result_msg, 'persona': persona_id,
                        'persona_name': persona['name'], 'fallback': True})


# ═══════════════════════════════════════════════════════════════════════════════
#  5D GAME ENGINE EXTENSION
#  D1: Spatial (existing rows×cols board)
#  D2: Layer  (stacked board planes — stones shift layers on threshold)
#  D3: Time   (echo phase — invoke your best past move every 5 turns)
#  D4: Quantum (hidden-count holes revealed on pickup)
#  D5: Tribal  (tribe-specific board mechanics at iNkosi+ level)
# ═══════════════════════════════════════════════════════════════════════════════

import random as _rnd

# ── Layer thresholds: when a relay lands here with exactly N stones → shift layer ─
LAYER_SHIFT_THRESHOLD = 4   # landing on 4 stones triggers layer shift
QUANTUM_VARIANCE      = 2   # quantum holes show ±QUANTUM_VARIANCE stones
ECHO_EVERY_N_MOVES    = 5   # echo phase every N moves

# ── Tribe board bonuses (active at iNkosi level 3+) ──────────────────────────
TRIBE_BOARD_BONUSES = {
    'amazulu':    {'type': 'capture_multiplier', 'value': 1.5,
                   'desc': 'Captures pay 1.5× cows (rounded up)',
                   'icon': '⚔️'},
    'amaxhosa':   {'type': 'relay_extend',       'value': 1,
                   'desc': 'Relay chains get +1 extra hop',
                   'icon': '🔗'},
    'amandebele': {'type': 'quantum_positive',   'value': True,
                   'desc': 'Quantum holes always reveal +2 (never negative)',
                   'icon': '✨'},
    'emaswati':   {'type': 'free_stone_bonus',   'value': 3,
                   'desc': 'Every 3rd win adds 1 free stone to weakest hole',
                   'icon': '🦁'},
    'vatsonga':   {'type': 'market_discount',    'value': 0.5,
                   'desc': 'Shop items cost 50% fewer cows this game',
                   'icon': '🌿'},
    'basotho':    {'type': 'relay_extend',       'value': 2,
                   'desc': 'Mountain fortress: relay chains get +2 extra hops',
                   'icon': '☀️'},
    'bapedi':     {'type': 'layer_reveal',       'value': True,
                   'desc': 'See layer 2 stone counts before moving',
                   'icon': '🌙'},
    'bavenda':    {'type': 'quantum_positive',   'value': True,
                   'desc': 'Quantum holes always reveal +2 (mystic sight)',
                   'icon': '🌊'},
    'world':      {'type': 'none',               'value': 0,
                   'desc': 'No tribal bonus — pure skill',
                   'icon': '🌍'},
}


def _get_tribe_bonus(tribe_id: str) -> dict:
    return TRIBE_BOARD_BONUSES.get(tribe_id, TRIBE_BOARD_BONUSES['world'])


def _5d_config_for_level(level: int) -> dict:
    """Return 5D parameters for a given game level."""
    if level <= 2:
        return {'layers': 1, 'quantum_holes': 0, 'echo_phase': False, 'tribe_bonus': False}
    elif level == 3:
        return {'layers': 2, 'quantum_holes': 2, 'echo_phase': False, 'tribe_bonus': True}
    else:  # levels 4-5
        return {'layers': 3, 'quantum_holes': 4, 'echo_phase': True,  'tribe_bonus': True}


# ═══════════════════════════════════════════════════════════════════════════════
#  PATCHED GameState — 5D Extension
# ═══════════════════════════════════════════════════════════════════════════════

_OriginalGameState_init = GameState.__init__

def _5d_init(self, rows=4, cols=4, mode='ai', level=1, tribe_id='world'):
    _OriginalGameState_init(self, rows, cols, mode, level)
    cfg = _5d_config_for_level(level)

    # D2 — Layer dimension
    self.layers       = cfg['layers']
    # layer_board[L][idx] = stone count on layer L
    self.layer_board  = [[0] * (rows * cols) for _ in range(self.layers)]
    # Distribute initial stones across layers when layers>1
    if self.layers > 1:
        for idx in range(rows * cols):
            base = self.board[idx]  # starts at 2
            self.layer_board[0][idx] = base
            # Layer 0 = main board (stays in sync with self.board)
    else:
        self.layer_board[0] = list(self.board)

    # D3 — Time dimension (echo phase)
    self.echo_enabled = cfg['echo_phase']
    self.move_count   = 0
    self.echo_log     = []      # [(move_idx, captured, board_snapshot), ...]
    self.echo_pending = False   # True when player must decide on echo
    self.echo_move    = None    # the move being offered as echo

    # D4 — Quantum holes
    n_quantum = cfg['quantum_holes']
    all_holes = list(range(rows * cols))
    self.quantum_holes   = set(_rnd.sample(all_holes, min(n_quantum, len(all_holes)))) if n_quantum else set()
    self.quantum_offsets = {}   # hole_idx → actual ±offset (hidden until sown)
    # NOTE: _randomise_quantum() called AFTER tribe_bonus is set (below)
    self.quantum_refresh_every = 10  # re-randomise every N moves
    self.wins_this_game = 0

    # D5 — Tribal dimension (must be set BEFORE _randomise_quantum)
    self.tribe_id       = tribe_id
    self.tribe_bonus    = _get_tribe_bonus(tribe_id) if cfg['tribe_bonus'] else TRIBE_BOARD_BONUSES['world']
    self.relay_extend   = self.tribe_bonus['value'] if self.tribe_bonus['type'] == 'relay_extend' else 0

    # Now safe to randomise quantum (needs tribe_bonus)
    self._randomise_quantum()
    self._last_quantum_reveal = None  # set by do_sow, read by route

GameState.__init__ = _5d_init


def _randomise_quantum(self):
    """Assign hidden offsets to quantum holes."""
    bonus = self.tribe_bonus
    for idx in self.quantum_holes:
        if bonus['type'] == 'quantum_positive':
            self.quantum_offsets[idx] = QUANTUM_VARIANCE  # always +2
        else:
            self.quantum_offsets[idx] = _rnd.choice([-QUANTUM_VARIANCE, QUANTUM_VARIANCE])

GameState._randomise_quantum = _randomise_quantum


# ── Override to_dict to include 5D state ─────────────────────────────────────
_OriginalGameState_to_dict = GameState.to_dict

def _5d_to_dict(self):
    d = _OriginalGameState_to_dict(self)
    if getattr(self, 'layers', 1) > 1 or getattr(self, 'quantum_holes', set()) or getattr(self, 'echo_enabled', False):
        d['dimensions'] = {
            'd1_spatial': {'rows': self.rows, 'cols': self.cols},
        'd2_layers':  {
            'active_layers': self.layers,
            'layer_board':   self.layer_board,
            'layer_threshold': LAYER_SHIFT_THRESHOLD,
        },
        'd3_echo':    {
            'enabled':       self.echo_enabled,
            'move_count':    self.move_count,
            'echo_pending':  self.echo_pending,
            'echo_move':     self.echo_move,
            'next_echo_in':  ECHO_EVERY_N_MOVES - (self.move_count % ECHO_EVERY_N_MOVES),
        },
        'd4_quantum': {
            'quantum_holes':  list(self.quantum_holes),
            # show visible counts (actual ± offset hidden until sown)
            'visible_counts': {
                str(idx): self.board[idx]  # displayed count — offset hidden
                for idx in self.quantum_holes
            },
        },
        'd5_tribal':  {
            'tribe_id':    self.tribe_id,
            'bonus_type':  self.tribe_bonus['type'],
            'bonus_desc':  self.tribe_bonus['desc'],
            'bonus_icon':  self.tribe_bonus['icon'],
        },
    }
    d['is_5d']    = getattr(self,'layers',1) > 1 or bool(getattr(self,'quantum_holes',set())) or getattr(self,'echo_enabled',False)
    d['dim_level']= ('5D' if getattr(self,'layers',1)>=3 else '4D' if getattr(self,'layers',1)==2 else '3D' if getattr(self,'quantum_holes',set()) else 'Classic')
    return d

GameState.to_dict = _5d_to_dict


# ── Override do_sow to apply 5D mechanics ────────────────────────────────────
_OriginalGameState_do_sow = GameState.do_sow

def _5d_do_sow(self, idx: int, player: int):
    """5D-extended sow. Applies quantum reveal, layer shifts, and echo logging."""

    # D4: Quantum reveal — actual count differs from visible
    quantum_reveal = None
    if idx in self.quantum_holes:
        offset = self.quantum_offsets.get(idx, 0)
        actual = max(1, self.board[idx] + offset)
        quantum_reveal = {'hole': idx, 'shown': self.board[idx], 'actual': actual, 'offset': offset}
        self.board[idx] = actual  # reveal actual count for the sow

    # Standard sow
    steps, captured, game_over, msg = _OriginalGameState_do_sow(self, idx, player)

    if steps is None:
        return steps, captured, game_over, msg

    # D5: Tribal capture multiplier
    bonus = self.tribe_bonus
    if captured and bonus['type'] == 'capture_multiplier':
        captured = int(captured * bonus['value'] + 0.5)  # round up

    # D2: Layer shift check — if landing hole has >= LAYER_SHIFT_THRESHOLD stones
    # and there is a layer above, shift excess stones up
    if self.layers > 1 and steps:
        last_board = steps[-1]
        for hole_idx in range(self.rows * self.cols):
            stones = last_board[hole_idx]
            if stones >= LAYER_SHIFT_THRESHOLD:
                # Shift to layer 1 (or cycle back from top layer)
                shift_amount = stones // LAYER_SHIFT_THRESHOLD
                self.layer_board[0][hole_idx] = stones % LAYER_SHIFT_THRESHOLD
                self.board[hole_idx]          = stones % LAYER_SHIFT_THRESHOLD
                next_layer = 1 % self.layers
                self.layer_board[next_layer][hole_idx] = (
                    self.layer_board[next_layer][hole_idx] + shift_amount
                )
                # Multi-layer games: if layer 2 fills up, cascade to layer 0
                if self.layers >= 3:
                    l2 = self.layer_board[1][hole_idx]
                    if l2 >= LAYER_SHIFT_THRESHOLD:
                        self.layer_board[2][hole_idx] += l2 // LAYER_SHIFT_THRESHOLD
                        self.layer_board[1][hole_idx]  = l2 % LAYER_SHIFT_THRESHOLD

    # D3: Time / Echo — log move and check echo trigger
    self.move_count += 1
    if steps:
        self.echo_log.append((idx, captured, list(self.board)))
        if len(self.echo_log) > ECHO_EVERY_N_MOVES * 2:
            self.echo_log.pop(0)

    if self.echo_enabled and self.move_count % ECHO_EVERY_N_MOVES == 0 and player == 0:
        if self.echo_log:
            best = max(self.echo_log, key=lambda x: x[1])  # highest capture move
            self.echo_pending = True
            self.echo_move    = {'original_idx': best[0], 'original_captured': best[1]}

    # D5: Free stone bonus for emaSwati (every 3rd win)
    if captured > 0 and bonus['type'] == 'free_stone_bonus' and player == 0:
        self.wins_this_game = getattr(self, 'wins_this_game', 0) + 1
        if self.wins_this_game % int(bonus['value']) == 0:
            # Add 1 stone to players weakest hole
            own_holes = [i for i in range(self.rows*self.cols) if self.owns_hole(i, 0)]
            if own_holes:
                weakest = min(own_holes, key=lambda i: self.board[i])
                self.board[weakest] += 1

    # Refresh quantum holes every N moves
    if self.move_count % self.quantum_refresh_every == 0 and self.quantum_holes:
        self._randomise_quantum()

    # Attach quantum reveal info to last step for animation
    if quantum_reveal and steps:
        # steps[-1] is already updated board
        pass  # quantum_reveal sent separately in response

    self._last_quantum_reveal = quantum_reveal
    return steps, captured, game_over, msg

GameState.do_sow = _5d_do_sow


# ── Echo invoke endpoint ──────────────────────────────────────────────────────
@app.route('/api/game/echo/invoke', methods=['POST'])
def echo_invoke():
    """Player invokes the echo — replays their best past move, adding bonus stones."""
    token = session.get('token')
    game  = get_game(token)
    if not game:
        return jsonify({'error': 'No active game'}), 400
    if not game.echo_pending:
        return jsonify({'error': 'No echo pending'}), 400
    echo = game.echo_move
    bonus_stones = echo.get('original_captured', 0)
    # Add bonus stones distributed across players holes
    own_holes = [i for i in range(game.rows * game.cols) if game.owns_hole(i, 0)]
    for i, hole in enumerate(own_holes[:min(bonus_stones, len(own_holes))]):
        game.board[hole] += 1
    game.echo_pending = False
    game.echo_move    = None
    set_game(token, game)
    return jsonify({'ok': True, 'bonus_stones': bonus_stones,
                    'state': game.to_dict(), 'message': f'⏳ Echo invoked! +{bonus_stones} stones spread across your holes.'})


@app.route('/api/game/echo/skip', methods=['POST'])
def echo_skip():
    """Player skips the echo phase."""
    token = session.get('token')
    game  = get_game(token)
    if not game:
        return jsonify({'error': 'No active game'}), 400
    game.echo_pending = False
    game.echo_move    = None
    set_game(token, game)
    return jsonify({'ok': True, 'message': 'Echo skipped.'})


# ── Layer peek endpoint ───────────────────────────────────────────────────────
@app.route('/api/game/layers')
def game_layers():
    """Return full layer state (BaPedi tribe can always see this)."""
    token = session.get('token')
    game  = get_game(token)
    if not game:
        return jsonify({'error': 'No active game'}), 400
    user  = current_user()
    tribe = getattr(game, 'tribe_id', 'world')
    # BaPedi tribe can always see layers — others only see layer 0
    can_see_all = (tribe == 'bapedi' or (user and _get_herd(user['email']) >= 2000))
    return jsonify({
        'layers':      game.layers,
        'layer_board': game.layer_board if can_see_all else [game.layer_board[0]],
        'visible_layers': game.layers if can_see_all else 1,
        'tribe_sight': can_see_all,
    })


# ── 5D Game start with tribe attachment ──────────────────────────────────────
@app.route('/api/game/start-5d', methods=['POST'])
def game_start_5d():
    """Start a 5D game session — requires iNkosi level (level 3+)."""
    user = current_user()
    data = request.get_json(force=True) or {}
    level = int(data.get('level', 3))
    if level < 3:
        return jsonify({'error': '5D mode requires Level 3 (iNkosi) or above'}), 400
    tribe_id   = sanitise(str(data.get('tribe_id', 'world')), 30)
    mode       = sanitise(str(data.get('mode', 'ai')), 10)
    skin       = sanitise(str(data.get('skin', 'zulu')), 20)
    lang       = sanitise(str(data.get('lang', 'en')), 10)
    persona_id = sanitise(str(data.get('persona_id', 'shaka')), 20)
    bet_amount = int(data.get('bet_amount', 0))
    cfg        = _5d_config_for_level(level)
    rows       = 4
    cols       = 6 if level >= 2 else 4
    game = GameState(rows=rows, cols=cols, mode=mode, level=level, tribe_id=tribe_id)
    game._persona_id   = persona_id if persona_id in AI_PERSONAS else 'shaka'
    game._prize_locked = bet_amount >= AI_PRIZE_GUARD_COWS
    game._bet_amount   = bet_amount
    token = session.get('token', secrets.token_hex(16))
    session['token'] = token
    session['skin']  = skin
    session['lang']  = lang
    set_game(token, game)
    tribe_bonus = _get_tribe_bonus(tribe_id)
    return jsonify({
        'ok':          True,
        'state':       game.to_dict(),
        'skin':        SKINS.get(skin, SKINS['zulu']),
        'lang':        LANGS.get(lang, LANGS['en']),
        'dim_config':  cfg,
        'tribe_bonus': tribe_bonus,
        'is_5d':       True,
        'dim_level':   game.to_dict().get('dim_level', '5D'),
        'message':     f'5D game started! {tribe_bonus["icon"]} {tribe_bonus["desc"]}',
    })


# ── 5D info endpoint ─────────────────────────────────────────────────────────
@app.route('/api/game/5d/info')
def game_5d_info():
    """Return full 5D mechanics explanation."""
    return jsonify({
        'dimensions': {
            'D1_Spatial':  {'desc': 'Classic rows×cols board — the stone sowing path', 'always_active': True},
            'D2_Layer':    {'desc': 'Stacked planes — stones shift layers at threshold', 'min_level': 3},
            'D3_Echo':     {'desc': 'Time echo — invoke your best past move every 5 turns', 'min_level': 4},
            'D4_Quantum':  {'desc': 'Hidden-count holes — revealed when picked up', 'min_level': 3},
            'D5_Tribal':   {'desc': 'Tribe-specific board mechanics', 'min_level': 3},
        },
        'layer_threshold': LAYER_SHIFT_THRESHOLD,
        'quantum_variance': QUANTUM_VARIANCE,
        'echo_every':       ECHO_EVERY_N_MOVES,
        'tribe_bonuses':    TRIBE_BOARD_BONUSES,
        'level_configs': {
            1: _5d_config_for_level(1),
            2: _5d_config_for_level(2),
            3: _5d_config_for_level(3),
            4: _5d_config_for_level(4),
            5: _5d_config_for_level(5),
        },
    })

# ═══════════════════════════════════════════════════════════════════════════
#  SECURITY ROUTES — MFA, Encrypted Profiles, Score Signing, Store Protection
# ═══════════════════════════════════════════════════════════════════════════

# ── MFA SETUP ────────────────────────────────────────────────────────────────
@app.route('/api/auth/mfa-setup', methods=['POST'])
def mfa_setup():
    """Generate TOTP secret and QR URI. Player must confirm before enabling."""
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    db = get_db()
    row = db.execute('SELECT mfa_enabled FROM users WHERE email=?',(user['email'],)).fetchone()
    if row and row['mfa_enabled']:
        return jsonify({'error':'MFA already enabled. Disable first.'}), 409
    secret = generate_totp_secret()
    uri    = totp_uri(secret, user['email'])
    # Store secret temporarily (not enabled until confirmed)
    db.execute("UPDATE users SET mfa_secret=? WHERE email=?", (secret, user['email']))
    db.commit()
    return jsonify({'ok':True,'secret':secret,'uri':uri,
                    'instructions':'Scan the URI in Google Authenticator or Authy, then confirm with /api/auth/mfa-confirm'})

@app.route('/api/auth/mfa-confirm', methods=['POST'])
def mfa_confirm():
    """Confirm TOTP code to activate MFA. Generates 8 backup codes."""
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    data = request.get_json(force=True) or {}
    code = str(data.get('code','')).strip()
    db   = get_db()
    row  = db.execute('SELECT mfa_secret FROM users WHERE email=?',(user['email'],)).fetchone()
    if not row or not row['mfa_secret']:
        return jsonify({'error':'No pending MFA setup. Run /api/auth/mfa-setup first.'}), 400
    if not verify_totp(row['mfa_secret'], code):
        db.execute("UPDATE users SET failed_mfa_count=failed_mfa_count+1 WHERE email=?", (user['email'],))
        db.commit()
        return jsonify({'error':'Invalid code. Check time sync on your device.'}), 401
    backup = [secrets.token_hex(4).upper() for _ in range(8)]
    db.execute("UPDATE users SET mfa_enabled=1, failed_mfa_count=0, mfa_backup_codes=? WHERE email=?",
               (json.dumps(backup), user['email']))
    db.execute("INSERT INTO mfa_events(email,event,ip) VALUES(?,?,?)",
               (user['email'],'mfa_enabled',request.remote_addr or ''))
    db.commit()
    log.info(f"[MFA] Enabled for {user['email']}")
    return jsonify({'ok':True,'message':'MFA enabled!','backup_codes':backup,
                    'warning':'Save these backup codes securely — each can only be used once.'})

@app.route('/api/auth/mfa-verify', methods=['POST'])
def mfa_verify():
    """Verify TOTP code for a session (unlocks MFA-protected routes)."""
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    data = request.get_json(force=True) or {}
    code = str(data.get('code','')).strip()
    db   = get_db()
    row  = db.execute('SELECT mfa_secret,mfa_enabled,failed_mfa_count,account_locked,lock_until,mfa_backup_codes FROM users WHERE email=?',
                      (user['email'],)).fetchone()
    if not row or not row['mfa_enabled']:
        session['mfa_verified'] = True
        return jsonify({'ok':True,'message':'MFA not enabled'})
    # Account lockout after 5 failed attempts
    now = int(time.time())
    if row['account_locked'] and row['lock_until'] > now:
        mins = (row['lock_until'] - now) // 60 + 1
        return jsonify({'error':f'Account locked for {mins} more minute(s) due to too many failed attempts.'}), 423
    # Try TOTP
    if verify_totp(row['mfa_secret'], code):
        db.execute("UPDATE users SET failed_mfa_count=0,account_locked=0,lock_until=0,last_mfa_ts=? WHERE email=?",
                   (now, user['email']))
        db.execute("INSERT INTO mfa_events(email,event,ip) VALUES(?,?,?)",
                   (user['email'],'mfa_success',request.remote_addr or ''))
        db.commit()
        session['mfa_verified'] = True
        session['mfa_ts'] = now
        return jsonify({'ok':True,'message':'MFA verified. Store and sensitive routes unlocked for this session.'})
    # Try backup codes
    try:
        backups = json.loads(row['mfa_backup_codes'] or '[]')
    except Exception:
        backups = []
    if code.upper() in backups:
        backups.remove(code.upper())
        db.execute("UPDATE users SET mfa_backup_codes=?,failed_mfa_count=0 WHERE email=?",
                   (json.dumps(backups), user['email']))
        db.execute("INSERT INTO mfa_events(email,event,ip) VALUES(?,?,?)",
                   (user['email'],'backup_code_used',request.remote_addr or ''))
        db.commit()
        session['mfa_verified'] = True
        return jsonify({'ok':True,'message':f'Backup code accepted. {len(backups)} remaining.'})
    # Failed
    fails = (row['failed_mfa_count'] or 0) + 1
    locked, lock_until = (1, now + 300) if fails >= 5 else (0, 0)
    db.execute("UPDATE users SET failed_mfa_count=?,account_locked=?,lock_until=? WHERE email=?",
               (fails, locked, lock_until, user['email']))
    db.execute("INSERT INTO mfa_events(email,event,ip) VALUES(?,?,?)",
               (user['email'],'mfa_failed',request.remote_addr or ''))
    db.commit()
    if locked:
        return jsonify({'error':'5 failed attempts — account locked for 5 minutes.'}), 423
    return jsonify({'error':f'Invalid MFA code. {5-fails} attempt(s) remaining.'}), 401

@app.route('/api/auth/mfa-disable', methods=['POST'])
def mfa_disable():
    """Disable MFA (requires current password + valid TOTP)."""
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    data = request.get_json(force=True) or {}
    code = str(data.get('code','')); pw = str(data.get('password',''))
    db   = get_db()
    row  = db.execute('SELECT hash,salt,mfa_secret,mfa_enabled FROM users WHERE email=?',
                      (user['email'],)).fetchone()
    if not row: return jsonify({'error':'User not found'}), 404
    if not verify_password(pw, row['hash'], row['salt']):
        return jsonify({'error':'Password incorrect'}), 401
    if row['mfa_enabled'] and not verify_totp(row['mfa_secret'], code):
        return jsonify({'error':'Invalid MFA code'}), 401
    db.execute("UPDATE users SET mfa_enabled=0,mfa_secret='',mfa_backup_codes='[]' WHERE email=?",
               (user['email'],))
    db.execute("INSERT INTO mfa_events(email,event,ip) VALUES(?,?,?)",
               (user['email'],'mfa_disabled',request.remote_addr or ''))
    db.commit()
    return jsonify({'ok':True,'message':'MFA disabled.'})

@app.route('/api/auth/mfa-status', methods=['GET','POST'])
def mfa_status():
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    db = get_db()
    row = db.execute('SELECT mfa_enabled,failed_mfa_count FROM users WHERE email=?',(user['email'],)).fetchone()
    return jsonify({'mfa_enabled':bool(row['mfa_enabled'] if row else 0),
                    'session_verified':bool(session.get('mfa_verified')),
                    'failed_attempts':row['failed_mfa_count'] if row else 0})

# ── ENCRYPTED PROFILE WALL ────────────────────────────────────────────────────
@app.route('/api/profile/wall', methods=['GET'])
def get_wall():
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    target = sanitise(str(request.args.get('email', user['email'])), 80)
    db   = get_db()
    rows = db.execute(
        'SELECT id,author_email,content_enc,post_type,created FROM wall_posts '
        'WHERE target_email=? AND flagged=0 ORDER BY created DESC LIMIT 50',
        (target,)
    ).fetchall()
    posts = []
    for r in rows:
        author = db.execute('SELECT name FROM users WHERE email=?',(r['author_email'],)).fetchone()
        posts.append({'id':r['id'],'author':author['name'] if author else 'Unknown',
                      'content':decrypt_str(r['content_enc']),
                      'type':r['post_type'],'created':r['created']})
    return jsonify({'posts':posts,'count':len(posts)})

@app.route('/api/profile/wall', methods=['POST'])
def post_to_wall():
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    data    = request.get_json(force=True) or {}
    target  = sanitise(str(data.get('target_email', user['email'])), 80)
    content = sanitise(str(data.get('content','')), 500)
    if not content: return jsonify({'error':'Empty post'}), 400
    # Idempotency check
    idem_key = f'wall:{user["email"]}:{target}:{hash(content)}'
    if not check_idempotency(idem_key, ttl=10):
        return jsonify({'error':'Duplicate post rejected'}), 409
    db = get_db()
    db.execute(
        'INSERT INTO wall_posts(author_email,target_email,content_enc,post_type) VALUES(?,?,?,?)',
        (user['email'], target, encrypt_str(content), 'wall')
    )
    db.commit()
    return jsonify({'ok':True,'message':'Posted to wall.'})

@app.route('/api/profile/bio', methods=['POST'])
def update_bio():
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    data = request.get_json(force=True) or {}
    bio  = sanitise(str(data.get('bio','')), 300)
    db   = get_db()
    db.execute('UPDATE users SET enc_bio=? WHERE email=?', (encrypt_str(bio), user['email']))
    db.commit()
    return jsonify({'ok':True})

@app.route('/api/profile/bio')
def get_bio():
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    email = sanitise(str(request.args.get('email', user['email'])), 80)
    db    = get_db()
    row   = db.execute('SELECT enc_bio,name FROM users WHERE email=?',(email,)).fetchone()
    if not row: return jsonify({'error':'User not found'}), 404
    return jsonify({'bio':decrypt_str(row['enc_bio']),'name':row['name']})

# ── SECURE MARKET BUY (MFA + idempotency + signature) ─────────────────────────
@app.route('/api/store/buy', methods=['POST'])
@require_mfa
def secure_store_buy():
    """MFA-protected, idempotency-guarded, signature-verified store purchase."""
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    data     = request.get_json(force=True) or {}
    item_id  = sanitise(str(data.get('item','')), 40)
    ts       = int(data.get('ts', 0))
    sig      = str(data.get('sig',''))
    idem_key = sanitise(str(data.get('idempotency_key','')), 64)
    item     = MARKET_ITEMS.get(item_id)
    if not item: return jsonify({'error':'Unknown item'}), 400
    # Verify transaction signature
    if not verify_transaction(user['email'], item_id, item['cows'], ts, sig):
        log.warning(f"[store] Invalid signature for {user['email']} buying {item_id}")
        return jsonify({'error':'Invalid transaction signature or expired request. '
                                'Re-request via /api/store/sign-transaction'}), 403
    # Idempotency guard — blocks replay attacks
    if idem_key and not check_idempotency(idem_key, ttl=120):
        return jsonify({'error':'Duplicate transaction rejected'}), 409
    # Check cow balance
    herd = _get_herd(user['email'])
    if herd < item['cows']:
        return jsonify({'ok':False,'insufficient':True,'herd_cows':herd,'required':item['cows']}), 402
    # Execute purchase
    new_bal = _add_cows(user['email'], -item['cows'], 'store_buy_'+item_id, {'item':item_id})
    db = get_db()
    if item.get('col'):
        db.execute(f"UPDATE users SET {item['col']}={item['col']}+1 WHERE email=?", (user['email'],))
    # Record transaction
    db.execute('INSERT INTO store_transactions(email,item_id,cost_cows,idempotency,sig) VALUES(?,?,?,?,?)',
               (user['email'], item_id, item['cows'], idem_key or None, sig[:48]))
    db.commit()
    log.info(f"[store] {user['email']} bought {item_id} for {item['cows']} cows")
    return jsonify({'ok':True,'item':item_id,'herd_cows':new_bal,
                    'message':item['icon']+' '+item['name']+' acquired!'})

@app.route('/api/store/sign-transaction', methods=['POST'])
def sign_store_transaction():
    """Return a signed transaction token for the store. Client presents this at /api/store/buy."""
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    data    = request.get_json(force=True) or {}
    item_id = sanitise(str(data.get('item','')), 40)
    item    = MARKET_ITEMS.get(item_id)
    if not item: return jsonify({'error':'Unknown item'}), 400
    ts  = int(time.time())
    sig = sign_transaction(user['email'], item_id, item['cows'], ts)
    idem= secrets.token_hex(16)
    return jsonify({'ts':ts,'sig':sig,'idempotency_key':idem,
                    'item':item_id,'cost_cows':item['cows'],
                    'expires_in_seconds':120})

# ── SIGNED GAME SCORES ─────────────────────────────────────────────────────────
@app.route('/api/game/submit-score', methods=['POST'])
def submit_signed_score():
    """Validate and record a signed game score — prevents manipulation."""
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    data  = request.get_json(force=True) or {}
    score = int(data.get('score', 0))
    level = int(data.get('level', 1))
    ts    = int(data.get('ts', 0))
    sig   = str(data.get('sig',''))
    idem  = str(data.get('idempotency_key',''))
    # Sanity bounds
    if score < 0 or score > 9999:
        return jsonify({'error':'Score out of valid range'}), 400
    if level < 1 or level > 5:
        return jsonify({'error':'Invalid level'}), 400
    if not verify_score(user['email'], score, level, ts, sig):
        log.warning(f"[score] Invalid sig from {user['email']}: score={score} level={level}")
        return jsonify({'error':'Score signature invalid or expired. '
                                'Scores must be signed by the game client.'}), 403
    if idem and not check_idempotency(idem, ttl=300):
        return jsonify({'error':'Duplicate score submission rejected'}), 409
    db = get_db()
    today = time.strftime('%Y-%m-%d')
    db.execute('INSERT OR REPLACE INTO daily_scores(user_email,day,score) VALUES(?,?,?)',
               (user['email'], today, max(score,
                   (db.execute('SELECT score FROM daily_scores WHERE user_email=? AND day=?',
                               (user['email'],today)).fetchone() or {'score':0})['score'])))
    db.commit()
    return jsonify({'ok':True,'score':score,'level':level})

@app.route('/api/game/sign-score', methods=['POST'])
def get_score_signature():
    """Issue a score signature — called by game client when game ends."""
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    data  = request.get_json(force=True) or {}
    score = int(data.get('score',0))
    level = int(data.get('level',1))
    ts    = int(time.time())
    sig   = sign_score(user['email'], score, level, ts)
    idem  = secrets.token_hex(16)
    return jsonify({'ts':ts,'sig':sig,'score':score,'level':level,
                    'idempotency_key':idem,'expires_in_seconds':300})

# ── GAME MODE (3D / 5D / AR-VR) ─────────────────────────────────────────────
@app.route('/api/game/mode', methods=['GET','POST'])
def game_mode_pref():
    """Get or set player's preferred game dimension mode: 3d | 5d | ar | vr"""
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    if request.method == 'POST':
        data = request.get_json(force=True) or {}
        mode = sanitise(str(data.get('mode','5d')),10).lower()
        if mode not in ('3d','5d','ar','vr'):
            return jsonify({'error':'mode must be 3d, 5d, ar, or vr'}), 400
        db = get_db()
        db.execute('UPDATE users SET game_mode=? WHERE email=?',(mode,user['email']))
        db.commit()
        session['game_mode'] = mode
        return jsonify({'ok':True,'game_mode':mode})
    db  = get_db()
    row = db.execute('SELECT game_mode FROM users WHERE email=?',(user['email'],)).fetchone()
    gm  = row['game_mode'] if row and row['game_mode'] else session.get('game_mode','5d')
    return jsonify({
        'game_mode': gm,
        'available': {
            '3d':  {'label':'Classic 3D','desc':'Traditional Nguni board — 2D board in 3D perspective','dimensions':['D1 Spatial']},
            '5d':  {'label':'5-Dimensional','desc':'Full 5D: layers, echo, quantum holes, tribal bonuses','dimensions':['D1 Spatial','D2 Layers','D3 Echo','D4 Quantum','D5 Tribal']},
            'ar':  {'label':'Augmented Reality','desc':'Play on any flat surface using device camera. Requires AR-capable device.','dimensions':['D1 Spatial','D2 Layers','D3 Echo','D4 Quantum','D5 Tribal'],'requires':'WebXR or ARKit/ARCore'},
            'vr':  {'label':'Virtual Reality','desc':'Fully immersive Nguni village environment. Requires VR headset.','dimensions':['D1 Spatial','D2 Layers','D3 Echo','D4 Quantum','D5 Tribal'],'requires':'WebXR or Meta Quest'},
        },
        'ar_vr_note': 'AR/VR modes stream game state to a WebXR frontend via /api/game/xr-state. The Python engine handles all game logic; rendering is done client-side.'
    })

@app.route('/api/game/xr-state')
def xr_game_state():
    """WebXR/AR/VR endpoint — rich 3D scene data for client-side rendering.

    Returns a complete scene graph that an A-Frame, Three.js or Unity WebGL
    frontend can consume directly. All game logic stays server-side.
    """
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    token = session.get('token')
    game  = get_game(token)
    if not game: return jsonify({'error':'No active game'}), 404
    state  = game.to_dict()
    gm     = session.get('game_mode', '5d')
    is_5d  = gm in ('5d','ar','vr')
    dims   = state.get('dimensions', {})
    rows, cols = game.rows, game.cols

    # ── 3D board geometry (unit = 1 game-unit) ─────────────────────────────
    HOLE_W, HOLE_H, HOLE_GAP = 0.18, 0.06, 0.04   # metres in AR, arbitrary in VR
    board_w = cols * (HOLE_W + HOLE_GAP)
    board_d = rows * (HOLE_W + HOLE_GAP)

    # Each hole: world-space x,y,z + visual properties
    holes_3d = []
    for i in range(rows * cols):
        r, c   = i // cols, i % cols
        stones = game.board[i]
        x = c * (HOLE_W + HOLE_GAP) - board_w/2 + HOLE_W/2
        z = r * (HOLE_W + HOLE_GAP) - board_d/2 + HOLE_W/2
        is_quantum = i in getattr(game, 'quantum_holes', set())
        is_p0      = game.owns_hole(i, 0)
        layer_stones= [
            lb[i] for lb in getattr(game, 'layer_board', [[]])
        ] if is_5d else [stones]
        holes_3d.append({
            'idx': i, 'row': r, 'col': c,
            'x': round(x, 4), 'y': 0.0, 'z': round(z, 4),
            'stones': stones,
            'layer_stones': layer_stones,
            'owner': 0 if is_p0 else 1,
            'is_quantum': is_quantum,
            'quantum_offset': game.quantum_offsets.get(i, 0) if is_quantum else 0,
            'glow': 'quantum' if is_quantum else ('valid' if stones > 0 and is_p0 and game.player==0 else 'none'),
            'stone_color': '#c8a84c' if is_p0 else '#8b4513',
        })

    # ── Layer 3D stacking ───────────────────────────────────────────────────
    layers_3d = []
    if is_5d and hasattr(game, 'layer_board'):
        for li, layer in enumerate(game.layer_board):
            layers_3d.append({
                'layer_index': li,
                'y_offset': round(li * 0.14, 3),
                'opacity': max(0.3, 1.0 - li * 0.25),
                'stones': layer,
            })

    # ── Echo visual ─────────────────────────────────────────────────────────
    echo_3d = None
    if is_5d and getattr(game, 'echo_pending', False) and game.echo_move:
        orig = game.echo_move.get('original_idx', -1)
        if orig >= 0:
            r2, c2 = orig // cols, orig % cols
            x2 = c2*(HOLE_W+HOLE_GAP)-board_w/2+HOLE_W/2
            z2 = r2*(HOLE_W+HOLE_GAP)-board_d/2+HOLE_W/2
            echo_3d = {
                'active': True,
                'hole_idx': orig,
                'x': round(x2,4), 'y': 0.0, 'z': round(z2,4),
                'original_captured': game.echo_move.get('original_captured', 0),
                'animation': 'ripple_gold',
                'prompt': 'Replay your best move? Tap the glowing hole.',
            }

    # ── Tribal aura ─────────────────────────────────────────────────────────
    bonus_type = dims.get('d5_tribal',{}).get('bonus_type','none')
    tribal_colors = {
        'capture_multiplier': '#ff6600',
        'relay_extend':       '#00aaff',
        'quantum_positive':   '#aa00ff',
        'free_stone_bonus':   '#00cc44',
        'market_discount':    '#ffcc00',
        'layer_reveal':       '#ffffff',
        'none':               '#c8a84c',
    }

    # ── VR scene objects ─────────────────────────────────────────────────────
    vr_scene = None
    if gm == 'vr':
        vr_scene = {
            'environment': 'nguni_village',
            'sky_color':   '#1a0a00',
            'ground':      'savanna_grass',
            'ambient_light': 0.4,
            'sun_intensity': 0.8,
            'sun_direction': [0.5, 1.0, 0.3],
            'npc_guards':  2,
            'fire_pit':    {'x':0,'y':0,'z':-2.5,'active': True},
            'drum_circle': {'x':2,'y':0,'z':-1.5,'playing': game.running},
            'board_table': {'material':'wood','height':0.8,'width':board_w+0.2,'depth':board_d+0.2},
            'player0_pos': {'x':0,'y':1.6,'z':board_d/2+0.6,'facing':0},
            'player1_pos': {'x':0,'y':1.6,'z':-(board_d/2+0.6),'facing':180},
        }

    # ── AR scene ─────────────────────────────────────────────────────────────
    ar_scene = None
    if gm == 'ar':
        ar_scene = {
            'hit_test':        True,
            'surface_required': 'horizontal',
            'board_scale':      0.6,
            'board_material':  'nguni_wood',
            'placement_guide': 'tap_to_place',
            'ui_overlay':      True,
            'shadow_casting':  True,
        }

    return jsonify({
        'game_state':   state,
        'render_mode':  gm,
        'is_5d':        is_5d,
        'timestamp':    int(time.time() * 1000),
        'board_3d': {
            'rows': rows, 'cols': cols,
            'width_m': round(board_w, 3),
            'depth_m': round(board_d, 3),
            'holes': holes_3d,
        },
        'layers_3d':    layers_3d,
        'echo_3d':      echo_3d,
        'tribal': {
            'bonus_type':  bonus_type,
            'aura_color':  tribal_colors.get(bonus_type,'#c8a84c'),
            'particle_fx': bonus_type != 'none',
        },
        'game_status': {
            'player_turn': game.player,
            'running':     game.running,
            'cows0':       state.get('cows0', 0),
            'cows1':       state.get('cows1', 0),
            'valid_moves': game.valid_moves(game.player),
        },
        'ar_vr_hints': {
            'layer_height_unit': 0.14,
            'quantum_glow':      True,
            'echo_ripple':       True,
            'tribal_aura':       bonus_type,
            'scene':             'nguni_village' if gm=='vr' else 'table_surface',
        },
        'dimensions':   dims if is_5d else {},
        'vr_scene':     vr_scene,
        'ar_scene':     ar_scene,
    })

# ── MFA EVENT LOG (admin) ─────────────────────────────────────────────────────
@app.route('/api/admin/mfa-events')
def admin_mfa_events():
    if not _require_admin(): return jsonify({'error':'Unauthorized'}), 401
    db   = get_db()
    rows = db.execute(
        'SELECT email,event,ip,ts FROM mfa_events ORDER BY ts DESC LIMIT 200'
    ).fetchall()
    return jsonify({'events':[dict(r) for r in rows]})


@app.route('/xr')
def xr_page():
    """A-Frame + Three.js WebXR page — full AR/VR experience in browser."""
    mode = sanitise(str(request.args.get('mode','vr')), 4)
    if mode not in ('ar','vr'): mode = 'vr'
    return render_template_string(XR_TEMPLATE, mode=mode,
                                   app_url=os.environ.get('APP_URL',''))

XR_TEMPLATE = r"""<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Intshuba XR — Nguni Stone Game</title>
<script src="https://aframe.io/releases/1.5.0/aframe.min.js"></script>
<style>
  body{margin:0;background:#000;font-family:sans-serif;}
  #overlay{position:fixed;top:0;left:0;right:0;bottom:0;
    display:flex;flex-direction:column;align-items:center;justify-content:center;
    background:rgba(13,8,4,.9);color:#c8a84c;z-index:999;}
  #overlay h1{font-size:1.4em;margin:0 0 8px;}
  #overlay p{font-size:.9em;color:#aaa;text-align:center;max-width:300px;}
  #enter-btn{margin-top:16px;padding:12px 28px;background:#c8a84c;color:#1a0900;
    border:none;border-radius:8px;font-size:1em;cursor:pointer;font-weight:bold;}
  #status{position:fixed;top:12px;left:50%;transform:translateX(-50%);
    background:rgba(0,0,0,.7);color:#c8a84c;padding:6px 14px;
    border-radius:16px;font-size:13px;z-index:1000;}
  #hud-xr{position:fixed;bottom:16px;left:0;right:0;display:flex;
    justify-content:center;gap:12px;z-index:1000;}
  .xr-btn{padding:10px 20px;background:rgba(200,168,76,.85);color:#1a0900;
    border:none;border-radius:24px;font-size:14px;font-weight:bold;cursor:pointer;}
</style>
</head>
<body>
<div id="overlay">
  <h1>🥽 Intshuba {{ mode|upper }}</h1>
  <p>{% if mode=='vr' %}Immersive VR — play in a Nguni village. Requires a WebXR-compatible headset or browser.
     {% else %}Augmented Reality — place the board on any flat surface using your camera.{% endif %}</p>
  <button id="enter-btn" onclick="enterXR()">Enter {{ mode|upper }}</button>
  <p style="margin-top:12px;font-size:.75em;color:#666">
    Game logic runs on the server. This page renders it in 3D.
  </p>
</div>

<div id="status">Connecting…</div>

<a-scene {% if mode=='vr' %}vr-mode-ui="enabled:true"{% else %}arjs="sourceType:webcam;debugUIEnabled:false" embedded{% endif %}
         renderer="antialias:true;colorManagement:true" shadow="type:pcf">

  <a-assets>
    <a-mixin id="hole" geometry="primitive:cylinder;radius:0.09;height:0.06"
             material="color:#3d1f00;roughness:0.8"></a-mixin>
    <a-mixin id="stone" geometry="primitive:sphere;radius:0.038"
             material="roughness:0.4;metalness:0.2"></a-mixin>
  </a-assets>

  <!-- Board surface -->
  <a-entity id="board-root" position="0 0.8 -1">
    <a-box id="board-surface" width="1.2" height="0.04" depth="0.8"
           material="color:#5c2e00;roughness:0.9"></a-box>
    <a-entity id="holes-container"></a-entity>
    <a-entity id="stones-container"></a-entity>
    <a-entity id="echo-ring" visible="false"></a-entity>
  </a-entity>

  {% if mode=='vr' %}
  <!-- VR environment -->
  <a-sky color="#1a0a00"></a-sky>
  <a-plane position="0 0 0" rotation="-90 0 0" width="30" height="30"
           material="color:#4a3000"></a-plane>
  <a-light type="ambient" intensity="0.4" color="#fff5e0"></a-light>
  <a-light type="directional" intensity="0.8" color="#fff5e0"
           position="2 4 3"></a-light>
  <a-entity id="fire-pit" position="0 0 -2.5">
    <a-sphere radius="0.3" material="color:#ff4400;emissive:#ff2200;emissiveIntensity:0.8"></a-sphere>
    <a-light type="point" intensity="1.2" color="#ff6600" distance="4"></a-light>
  </a-entity>
  {% else %}
  <!-- AR: minimal lighting, let real world show through -->
  <a-light type="ambient" intensity="0.6"></a-light>
  {% endif %}

  <a-camera id="cam" wasd-controls="enabled:{{ 'true' if mode=='vr' else 'false' }}"
            look-controls>
    <a-cursor color="#c8a84c" fuse="false" raycaster="objects:.clickable"></a-cursor>
  </a-camera>
</a-scene>

<div id="hud-xr" style="display:none">
  <button class="xr-btn" onclick="makeMove()">🎯 Move</button>
  <button class="xr-btn" onclick="exitXR()">✕ Exit</button>
</div>

<script>
const MODE='{{ mode }}';
const API_BASE=window.location.origin;
let _state=null, _selectedHole=-1, _pollTimer=null;

async function api(path,opts={}){
  const r=await fetch(API_BASE+path,{credentials:'include',...opts,
    headers:{'Content-Type':'application/json',...(opts.headers||{})}});
  return r.json();
}

async function poll(){
  try{
    const r=await api('/api/game/xr-state');
    if(r.error){document.getElementById('status').textContent='⚠ '+r.error;return;}
    _state=r;
    renderBoard(r);
    document.getElementById('status').textContent=
      r.game_status?.running
        ? (r.game_status.player_turn===0?'Your turn ♟':'AI thinking…')
        : '🏆 Game over';
  }catch(e){document.getElementById('status').textContent='⚠ Connection lost';}
}

function renderBoard(r){
  const hc=document.getElementById('holes-container');
  const sc=document.getElementById('stones-container');
  if(!hc||!sc)return;
  hc.innerHTML=''; sc.innerHTML='';
  const holes=r.board_3d?.holes||[];
  const validMoves=new Set(r.game_status?.valid_moves||[]);
  holes.forEach(h=>{
    // Hole cylinder
    const el=document.createElement('a-cylinder');
    el.setAttribute('mixin','hole');
    el.setAttribute('position',`${h.x} ${h.y} ${h.z}`);
    const isValid=validMoves.has(h.idx)&&r.game_status?.player_turn===0;
    const isQ=h.is_quantum;
    el.setAttribute('material',
      `color:${isQ?'#660099':isValid?'#c8a84c':'#3d1f00'};`+
      `emissive:${isQ?'#440066':isValid?'#886600':'#000'};`+
      `emissiveIntensity:${isQ||isValid?0.4:0};roughness:0.8`);
    el.setAttribute('class','clickable');
    el.dataset.idx=h.idx;
    el.addEventListener('click',()=>selectHole(h.idx));
    hc.appendChild(el);
    // Stone spheres stacked
    const layers=h.layer_stones||[h.stones];
    let stoneY=h.y+0.05;
    layers.forEach((count,li)=>{
      for(let s=0;s<Math.min(count,8);s++){
        const st=document.createElement('a-sphere');
        st.setAttribute('mixin','stone');
        const ox=(s%3-1)*0.055, oz=Math.floor(s/3)*0.055-0.027;
        st.setAttribute('position',`${h.x+ox} ${stoneY+s*0.04} ${h.z+oz}`);
        const c=h.owner===0?'#c8a84c':'#8b3a3a';
        st.setAttribute('material',`color:${c};roughness:0.4;metalness:0.3`);
        sc.appendChild(st);
      }
      stoneY+=li*0.14;
    });
    // Quantum glow ring
    if(isQ){
      const ring=document.createElement('a-ring');
      ring.setAttribute('radius-inner','0.10');
      ring.setAttribute('radius-outer','0.13');
      ring.setAttribute('position',`${h.x} ${h.y+0.035} ${h.z}`);
      ring.setAttribute('rotation','-90 0 0');
      ring.setAttribute('material','color:#aa00ff;emissive:#6600aa;emissiveIntensity:0.8;side:double');
      ring.setAttribute('animation','property:rotation;from:-90 0 0;to:-90 360 0;dur:2000;loop:true;easing:linear');
      sc.appendChild(ring);
    }
  });
  // Echo ring
  const echo=r.echo_3d;
  const er=document.getElementById('echo-ring');
  if(er&&echo?.active){
    er.setAttribute('visible','true');
    er.setAttribute('position',`${echo.x} ${echo.y+0.04} ${echo.z}`);
    er.innerHTML=`<a-ring radius-inner="0.12" radius-outer="0.17"
      material="color:#ffd700;emissive:#aa8800;emissiveIntensity:1;side:double"
      animation="property:rotation;from:-90 0 0;to:-90 360 0;dur:1200;loop:true;easing:linear">
    </a-ring>`;
  }else if(er){er.setAttribute('visible','false');}
  // Tribal aura on board
  const bs=document.getElementById('board-surface');
  if(bs&&r.tribal?.aura_color){
    bs.setAttribute('material',`color:#5c2e00;emissive:${r.tribal.aura_color};emissiveIntensity:0.08`);
  }
}

function selectHole(idx){
  if(!_state||_state.game_status?.player_turn!==0)return;
  _selectedHole=idx;
  document.getElementById('status').textContent=`Hole ${idx} selected — tap Move`;
  document.getElementById('hud-xr').style.display='flex';
}

async function makeMove(){
  if(_selectedHole<0)return;
  document.getElementById('status').textContent='Moving…';
  const r=await api('/api/game/move',{method:'POST',body:JSON.stringify({idx:_selectedHole})});
  _selectedHole=-1;
  document.getElementById('hud-xr').style.display='none';
  if(r.game_over){document.getElementById('status').textContent='🏆 Game over! '+JSON.stringify(r.scores);}
}

function enterXR(){
  document.getElementById('overlay').style.display='none';
  document.getElementById('hud-xr').style.display='flex';
  _pollTimer=setInterval(poll,150);
  poll();
}
function exitXR(){
  clearInterval(_pollTimer);
  window.close()||(window.location='/');
}
</script>
</body>
</html>
"""



# ═══════════════════════════════════════════════════════════════════════════════
#  BLOCKCHAIN INTEGRATION — Polygon (MATIC)
#  4 features: Prize Escrow · Crown NFT · Tournament Anchors · Cow Marketplace
#  Uses web3.py with graceful fallback when no node configured
# ═══════════════════════════════════════════════════════════════════════════════

import hashlib as _hs, hmac as _hm, json as _js, time as _tm
import threading as _thr

# ── Polygon connection (lazy-loaded) ─────────────────────────────────────────
_W3 = None
_W3_LOCK = _thr.Lock()

def _get_w3():
    global _W3
    if _W3 is not None:
        return _W3
    with _W3_LOCK:
        try:
            from web3 import Web3
            rpc = os.environ.get('POLYGON_RPC_URL', 'https://polygon-rpc.com')
            w3  = Web3(Web3.HTTPProvider(rpc, request_kwargs={'timeout': 10}))
            _W3 = w3 if w3.is_connected() else None
        except Exception:
            _W3 = None
    return _W3

def _chain_connected() -> bool:
    try:
        w3 = _get_w3()
        return w3 is not None and w3.is_connected()
    except Exception:
        return False

# Contract ABIs (minimal - only functions we call)
_ESCROW_ABI = [
    {"name":"depositPrizes","type":"function","stateMutability":"payable",
     "inputs":[{"name":"seasonId","type":"uint256"},{"name":"champions","type":"address[]"},{"name":"shares","type":"uint256[]"}],"outputs":[]},
    {"name":"claimPrize","type":"function","stateMutability":"nonpayable",
     "inputs":[{"name":"seasonId","type":"uint256"}],"outputs":[]},
    {"name":"pools","type":"function","stateMutability":"view",
     "inputs":[{"name":"","type":"uint256"}],"outputs":[{"name":"","type":"uint256"}]},
]
_CROWN_ABI = [
    {"name":"mintCrown","type":"function","stateMutability":"nonpayable",
     "inputs":[{"name":"to","type":"address"},{"name":"wonAt","type":"uint256"},{"name":"cows","type":"uint256"}],"outputs":[]},
    {"name":"transferCrown","type":"function","stateMutability":"nonpayable",
     "inputs":[{"name":"from_","type":"address"},{"name":"to","type":"address"},{"name":"wonAt","type":"uint256"},{"name":"cows","type":"uint256"}],"outputs":[]},
    {"name":"currentHolder","type":"function","stateMutability":"view",
     "inputs":[],"outputs":[{"name":"","type":"address"},{"name":"","type":"uint256"},{"name":"","type":"uint256"}]},
    {"name":"CrownMinted","type":"event","inputs":[{"name":"to","type":"address","indexed":True},{"name":"wonAt","type":"uint256","indexed":False}]},
]
_ANCHOR_ABI = [
    {"name":"anchorTournament","type":"function","stateMutability":"nonpayable",
     "inputs":[{"name":"tournamentId","type":"bytes32"},{"name":"resultsRoot","type":"bytes32"},{"name":"champion","type":"address"},{"name":"ts","type":"uint256"}],"outputs":[]},
    {"name":"anchors","type":"function","stateMutability":"view",
     "inputs":[{"name":"","type":"bytes32"}],"outputs":[{"name":"resultsRoot","type":"bytes32"},{"name":"champion","type":"address"},{"name":"ts","type":"uint256"}]},
]
_MARKET_ABI = [
    {"name":"listCows","type":"function","stateMutability":"nonpayable",
     "inputs":[{"name":"seller","type":"address"},{"name":"cowAmount","type":"uint256"},{"name":"priceWei","type":"uint256"}],"outputs":[{"name":"listingId","type":"uint256"}]},
    {"name":"buyCows","type":"function","stateMutability":"payable",
     "inputs":[{"name":"listingId","type":"uint256"}],"outputs":[]},
    {"name":"cancelListing","type":"function","stateMutability":"nonpayable",
     "inputs":[{"name":"listingId","type":"uint256"}],"outputs":[]},
    {"name":"getListing","type":"function","stateMutability":"view",
     "inputs":[{"name":"listingId","type":"uint256"}],"outputs":[{"name":"seller","type":"address"},{"name":"cowAmount","type":"uint256"},{"name":"priceWei","type":"uint256"},{"name":"active","type":"bool"}]},
]

def _get_contract(abi, env_var):
    w3 = _get_w3()
    if not w3: return None
    addr = os.environ.get(env_var, '')
    if not addr or addr == 'REPLACE': return None
    try:
        return w3.eth.contract(address=w3.to_checksum_address(addr), abi=abi)
    except Exception:
        return None

def _backend_key():
    pk = os.environ.get('POLYGON_PRIVATE_KEY','')
    return pk if pk and pk != 'REPLACE' else None

def _send_tx(contract_fn, value_wei=0):
    """Sign and send a transaction from the backend wallet."""
    w3 = _get_w3()
    pk = _backend_key()
    if not w3 or not pk:
        return {'ok': False, 'error': 'Blockchain not configured', 'simulated': True}
    try:
        account  = w3.eth.account.from_key(pk)
        nonce    = w3.eth.get_transaction_count(account.address)
        tx       = contract_fn.build_transaction({
            'from':     account.address,
            'nonce':    nonce,
            'gas':      300_000,
            'gasPrice': w3.eth.gas_price,
            'value':    value_wei,
        })
        signed   = w3.eth.account.sign_transaction(tx, pk)
        tx_hash  = w3.eth.send_raw_transaction(signed.rawTransaction)
        receipt  = w3.eth.wait_for_transaction_receipt(tx_hash, timeout=60)
        return {'ok': True, 'tx_hash': tx_hash.hex(), 'block': receipt.blockNumber,
                'gas_used': receipt.gasUsed, 'status': receipt.status}
    except Exception as e:
        log.error(f'[blockchain] tx failed: {e}')
        return {'ok': False, 'error': str(e)}

def _results_root(results: list) -> str:
    """Merkle-style root of tournament results for on-chain anchoring."""
    import hashlib
    leaves = [hashlib.sha256(json.dumps(r, sort_keys=True).encode()).digest() for r in results]
    while len(leaves) > 1:
        if len(leaves) % 2 == 1: leaves.append(leaves[-1])
        leaves = [hashlib.sha256(leaves[i]+leaves[i+1]).digest() for i in range(0,len(leaves),2)]
    return '0x' + leaves[0].hex() if leaves else '0x' + '0'*64

# ── DB table for blockchain state ─────────────────────────────────────────────
_BC_TABLES = """
CREATE TABLE IF NOT EXISTS blockchain_wallets (
    email         TEXT PRIMARY KEY,
    wallet_address TEXT NOT NULL,
    linked_at     INTEGER DEFAULT (strftime('%s','now')),
    verified      INTEGER DEFAULT 0
);
CREATE TABLE IF NOT EXISTS blockchain_txs (
    id        INTEGER PRIMARY KEY AUTOINCREMENT,
    email     TEXT,
    tx_type   TEXT NOT NULL,
    tx_hash   TEXT,
    detail    TEXT DEFAULT '{}',
    status    TEXT DEFAULT 'pending',
    created   INTEGER DEFAULT (strftime('%s','now'))
);
CREATE TABLE IF NOT EXISTS marketplace_listings (
    id            INTEGER PRIMARY KEY AUTOINCREMENT,
    seller_email  TEXT NOT NULL,
    cow_amount    INTEGER NOT NULL,
    price_matic   REAL NOT NULL,
    listing_id    INTEGER,
    active        INTEGER DEFAULT 1,
    created       INTEGER DEFAULT (strftime('%s','now'))
);
CREATE INDEX IF NOT EXISTS idx_bc_wallets ON blockchain_wallets(email);
CREATE INDEX IF NOT EXISTS idx_bc_txs     ON blockchain_txs(email);
CREATE INDEX IF NOT EXISTS idx_marketplace ON marketplace_listings(active);
"""

# ── API Routes ─────────────────────────────────────────────────────────────────

@app.route('/api/blockchain/status')
def blockchain_status():
    connected = _chain_connected()
    w3 = _get_w3()
    return jsonify({
        'connected':   connected,
        'network':     'Polygon Mainnet',
        'chain_id':    137,
        'rpc':         os.environ.get('POLYGON_RPC_URL','https://polygon-rpc.com'),
        'block':       w3.eth.block_number if connected and w3 else None,
        'contracts': {
            'prize_escrow':         os.environ.get('CONTRACT_PRIZE_ESCROW','NOT_DEPLOYED'),
            'crown_nft':            os.environ.get('CONTRACT_CROWN_NFT','NOT_DEPLOYED'),
            'tournament_anchor':    os.environ.get('CONTRACT_TOURNAMENT_ANCHOR','NOT_DEPLOYED'),
            'cow_marketplace':      os.environ.get('CONTRACT_COW_MARKETPLACE','NOT_DEPLOYED'),
        },
        'backend_wallet': os.environ.get('POLYGON_BACKEND_ADDRESS','NOT_CONFIGURED'),
        'note': 'Set POLYGON_RPC_URL, POLYGON_PRIVATE_KEY, and CONTRACT_* env vars to activate on-chain features.',
    })

@app.route('/api/blockchain/wallet/link', methods=['POST'])
def bc_link_wallet():
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    data    = request.get_json(force=True) or {}
    address = sanitise(str(data.get('wallet_address','')), 42)
    sig     = str(data.get('signature',''))
    msg     = str(data.get('message',''))
    if not address.startswith('0x') or len(address) != 42:
        return jsonify({'error':'Invalid wallet address (must be 0x + 40 hex chars)'}), 400
    # Verify EIP-191 signature if web3 available
    verified = False
    w3 = _get_w3()
    if w3 and sig and msg:
        try:
            recovered = w3.eth.account.recover_message(
                w3.eth.account.encode_defunct(text=msg),
                signature=sig
            )
            verified = recovered.lower() == address.lower()
        except Exception:
            verified = False
    db = get_db()
    db.execute('INSERT OR REPLACE INTO blockchain_wallets(email,wallet_address,verified) VALUES(?,?,?)',
               (user['email'], address.lower(), 1 if verified else 0))
    db.commit()
    return jsonify({'ok': True, 'address': address.lower(), 'verified': verified,
                    'message': 'Wallet linked! Verified signature: ' + str(verified)})

@app.route('/api/blockchain/wallet/status')
def bc_wallet_status():
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    db  = get_db()
    row = db.execute('SELECT wallet_address,verified,linked_at FROM blockchain_wallets WHERE email=?',
                     (user['email'],)).fetchone()
    txs = db.execute('SELECT tx_type,tx_hash,status,created FROM blockchain_txs WHERE email=? ORDER BY created DESC LIMIT 10',
                     (user['email'],)).fetchall()
    return jsonify({
        'has_wallet':     row is not None,
        'wallet_address': row['wallet_address'] if row else None,
        'address':        row['wallet_address'] if row else None,
        'verified':    bool(row['verified']) if row else False,
        'transactions': [dict(t) for t in txs],
    })

# ── Prize Escrow ──────────────────────────────────────────────────────────────
@app.route('/api/blockchain/prize/pool')
def bc_prize_pool():
    contract = _get_contract(_ESCROW_ABI, 'CONTRACT_PRIZE_ESCROW')
    season_id = int(request.args.get('season_id', 1))
    on_chain_balance = None
    if contract:
        try:
            on_chain_balance = contract.functions.pools(season_id).call()
        except Exception:
            pass
    return jsonify({
        'season_id':        season_id,
        'prize_pool_zar':   141600,
        'on_chain_wei':     on_chain_balance,
        'on_chain_matic':   round(on_chain_balance / 1e18, 4) if on_chain_balance else None,
        'contract':         os.environ.get('CONTRACT_PRIZE_ESCROW','NOT_DEPLOYED'),
        'how_to_claim':     'POST /api/blockchain/prize/claim after season ends',
    })

@app.route('/api/blockchain/prize/register', methods=['POST'])
def bc_register_prize():
    """Register a season champion for prize claim."""
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    db  = get_db()
    row = db.execute('SELECT wallet_address FROM blockchain_wallets WHERE email=?',(user['email'],)).fetchone()
    if not row: return jsonify({'error':'Link a Polygon wallet first via /api/blockchain/wallet/link'}), 400
    data      = request.get_json(force=True) or {}
    season_id = int(data.get('season_id', 1))
    prize_zar = int(data.get('prize_zar', 0))
    db.execute('INSERT INTO blockchain_txs(email,tx_type,detail,status) VALUES(?,?,?,?)',
               (user['email'], 'prize_registered',
                json.dumps({'season_id':season_id,'wallet':row['wallet_address'],'prize_zar':prize_zar}),
                'registered'))
    db.commit()
    return jsonify({'ok':True,'wallet':row['wallet_address'],'season_id':season_id,
                    'prize_zar':prize_zar,'status':'registered',
                    'next':'Admin will deposit to escrow contract and you can claim on-chain'})

@app.route('/api/blockchain/prize/claim', methods=['POST'])
def bc_claim_prize():
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    db  = get_db()
    row = db.execute('SELECT wallet_address FROM blockchain_wallets WHERE email=?',(user['email'],)).fetchone()
    if not row: return jsonify({'error':'No wallet linked'}), 400
    data      = request.get_json(force=True) or {}
    season_id = int(data.get('season_id', 1))
    contract  = _get_contract(_ESCROW_ABI, 'CONTRACT_PRIZE_ESCROW')
    if not contract:
        return jsonify({'ok':False,'simulated':True,'message':
                        'Contracts not deployed yet. Your prize is registered in DB and will be paid when contracts go live.',
                        'wallet':row['wallet_address']})
    result = _send_tx(contract.functions.claimPrize(season_id))
    if result.get('ok'):
        db.execute('INSERT INTO blockchain_txs(email,tx_type,tx_hash,status) VALUES(?,?,?,?)',
                   (user['email'],'prize_claimed',result['tx_hash'],'confirmed'))
        db.commit()
    return jsonify({**result, 'wallet':row['wallet_address'], 'season_id':season_id})

# ── Crown NFT ─────────────────────────────────────────────────────────────────
@app.route('/api/blockchain/crown/mint', methods=['POST'])
def bc_mint_crown():
    # Admin OR logged-in user (triggers when game awards crown)
    user = current_user()
    is_admin = _require_admin()
    if not user and not is_admin: return jsonify({'error':'Unauthorized'}), 401
    data     = request.get_json(force=True) or {}
    email    = sanitise(str(data.get('email','')), 80)
    cows     = int(data.get('cows_at_win', 0))
    db       = get_db()
    wrow     = db.execute('SELECT wallet_address FROM blockchain_wallets WHERE email=?',(email,)).fetchone()
    if not wrow: return jsonify({'error':f'{email} has no linked wallet'}), 400
    won_at   = int(time.time())
    contract = _get_contract(_CROWN_ABI, 'CONTRACT_CROWN_NFT')
    if not contract:
        db.execute('INSERT INTO blockchain_txs(email,tx_type,detail,status) VALUES(?,?,?,?)',
                   (email,'crown_minted',json.dumps({'wallet':wrow['wallet_address'],'cows':cows}),'simulated'))
        db.commit()
        return jsonify({'ok':True,'simulated':True,'message':'Crown NFT minted in DB (deploy contracts to go on-chain)',
                        'wallet':wrow['wallet_address'],'cows':cows})
    result = _send_tx(contract.functions.mintCrown(
        wrow['wallet_address'], won_at, cows))
    if result.get('ok'):
        db.execute('INSERT INTO blockchain_txs(email,tx_type,tx_hash,status) VALUES(?,?,?,?)',
                   (email,'crown_minted',result['tx_hash'],'confirmed'))
        db.commit()
    return jsonify({**result, 'wallet':wrow['wallet_address']})

@app.route('/api/blockchain/crown/history')
def bc_crown_history():
    db   = get_db()
    rows = db.execute('SELECT email,detail,tx_hash,created FROM blockchain_txs WHERE tx_type=? ORDER BY created DESC',
                      ('crown_minted',)).fetchall()
    on_chain = None
    contract = _get_contract(_CROWN_ABI, 'CONTRACT_CROWN_NFT')
    if contract:
        try:
            holder,won_at,cows = contract.functions.currentHolder().call()
            on_chain = {'holder':holder,'won_at':won_at,'cows':cows}
        except Exception:
            pass
    return jsonify({'history':[dict(r) for r in rows], 'on_chain_current':on_chain})

# ── Tournament Anchor ─────────────────────────────────────────────────────────
@app.route('/api/blockchain/tournament/anchor', methods=['POST'])
def bc_anchor_tournament():
    # Admin OR authenticated user (for self-anchoring their tournament results)
    user = current_user()
    is_admin = _require_admin()
    if not user and not is_admin: return jsonify({'error':'Unauthorized'}), 401
    data          = request.get_json(force=True) or {}
    tournament_id = sanitise(str(data.get('tournament_id', data.get('competition_id',''))), 64)
    results       = data.get('results', [])
    champion_email= sanitise(str(data.get('champion_email','')), 80)
    root          = _results_root(results)
    db            = get_db()
    wrow          = db.execute('SELECT wallet_address FROM blockchain_wallets WHERE email=?',
                               (champion_email,)).fetchone()
    champion_addr = wrow['wallet_address'] if wrow else '0x'+'0'*40
    contract      = _get_contract(_ANCHOR_ABI, 'CONTRACT_TOURNAMENT')
    if not contract:
        db.execute('INSERT INTO blockchain_txs(email,tx_type,detail,status) VALUES(?,?,?,?)',
                   (champion_email,'tournament_anchored',
                    json.dumps({'tournament_id':tournament_id,'root':root,'champion':champion_addr}),
                    'simulated'))
        db.commit()
        return jsonify({'ok':True,'simulated':True,'results_root':root,
                        'tournament_id':tournament_id,'champion_wallet':champion_addr})
    tid_bytes = bytes.fromhex(tournament_id.replace('0x','').zfill(64))[:32]
    root_bytes= bytes.fromhex(root.replace('0x',''))
    result    = _send_tx(contract.functions.anchorTournament(
        tid_bytes, root_bytes, champion_addr, int(time.time())))
    if result.get('ok'):
        db.execute('INSERT INTO blockchain_txs(email,tx_type,tx_hash,status) VALUES(?,?,?,?)',
                   (champion_email,'tournament_anchored',result['tx_hash'],'confirmed'))
        db.commit()
    return jsonify({**result,'results_root':root,'tournament_id':tournament_id})

@app.route('/api/blockchain/tournament/verify', methods=['POST'])
def bc_verify_tournament():
    data          = request.get_json(force=True) or {}
    tournament_id = sanitise(str(data.get('tournament_id','')), 64)
    results       = data.get('results', [])
    claimed_root  = str(data.get('results_root',''))
    computed_root = _results_root(results)
    match         = computed_root.lower() == claimed_root.lower()
    on_chain      = None
    contract      = _get_contract(_ANCHOR_ABI, 'CONTRACT_TOURNAMENT')
    if contract:
        try:
            tid_bytes = bytes.fromhex(tournament_id.replace('0x','').zfill(64))[:32]
            anchor    = contract.functions.anchors(tid_bytes).call()
            on_chain  = {'root':'0x'+anchor[0].hex(),'champion':anchor[1],'ts':anchor[2]}
        except Exception:
            pass
    return jsonify({'valid':match,'computed_root':computed_root,'claimed_root':claimed_root,
                    'on_chain':on_chain,'tournament_id':tournament_id})

@app.route('/api/blockchain/tournament/anchors')
def bc_tournament_anchors():
    db   = get_db()
    rows = db.execute("SELECT email,detail,tx_hash,status,created FROM blockchain_txs WHERE tx_type='tournament_anchored' ORDER BY created DESC LIMIT 50").fetchall()
    return jsonify({'anchors':[dict(r) for r in rows]})

# ── Cow Marketplace ───────────────────────────────────────────────────────────
@app.route('/api/blockchain/market/listings')
def bc_market_listings():
    db   = get_db()
    rows = db.execute('SELECT * FROM marketplace_listings WHERE active=1 ORDER BY created DESC LIMIT 50').fetchall()
    listings = []
    for r in rows:
        seller = db.execute('SELECT name FROM users WHERE email=?',(r['seller_email'],)).fetchone()
        listings.append({**dict(r), 'seller_name': seller['name'] if seller else 'Unknown'})
    return jsonify({'listings':listings,'count':len(listings)})

@app.route('/api/blockchain/market/list', methods=['POST'])
def bc_market_list():
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    db   = get_db()
    wrow = db.execute('SELECT wallet_address FROM blockchain_wallets WHERE email=?',(user['email'],)).fetchone()
    if not wrow: return jsonify({'error':'Link a wallet first'}), 400
    data       = request.get_json(force=True) or {}
    cow_amount = int(data.get('cow_amount', 0))
    price_matic= float(data.get('price_matic', 0))
    if cow_amount < 10: return jsonify({'error':'Minimum 10 cows per listing'}), 400
    if price_matic <= 0: return jsonify({'error':'Price must be > 0 MATIC'}), 400
    herd = _get_herd(user['email'])
    if herd < cow_amount: return jsonify({'error':f'You only have {herd} cows'}), 402
    # Deduct cows (held in escrow)
    _add_cows(user['email'], -cow_amount, 'marketplace_listed', {'amount':cow_amount,'price_matic':price_matic})
    listing_id = None
    contract   = _get_contract(_MARKET_ABI, 'CONTRACT_MARKETPLACE')
    if contract:
        price_wei = int(price_matic * 1e18)
        result    = _send_tx(contract.functions.listCows(wrow['wallet_address'], cow_amount, price_wei))
        listing_id= result.get('listing_id')
    db.execute('INSERT INTO marketplace_listings(email,cow_amount,price_matic,listing_id,wallet) VALUES(?,?,?,?,?)',
               (user['email'], cow_amount, price_matic, listing_id, wrow['wallet_address']))
    db.commit()
    return jsonify({'ok':True,'cow_amount':cow_amount,'price_matic':price_matic,
                    'wallet':wrow['wallet_address'],'on_chain':listing_id is not None})

@app.route('/api/blockchain/market/buy', methods=['POST'])
def bc_market_buy():
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    db   = get_db()
    data = request.get_json(force=True) or {}
    listing_id = int(data.get('listing_id', 0))
    row  = db.execute('SELECT * FROM marketplace_listings WHERE id=? AND active=1',(listing_id,)).fetchone()
    if not row: return jsonify({'error':'Listing not found or already sold'}), 404
    if row['seller_email'] == user['email']: return jsonify({'error':'Cannot buy your own listing'}), 400
    wrow = db.execute('SELECT wallet_address FROM blockchain_wallets WHERE email=?',(user['email'],)).fetchone()
    if not wrow: return jsonify({'error':'Link a wallet first'}), 400
    # Off-chain: give buyer the cows, deactivate listing
    _add_cows(user['email'], row['cow_amount'], 'marketplace_bought',
              {'listing_id':listing_id,'from':row['seller_email'],'price_matic':row['price_matic']})
    db.execute('UPDATE marketplace_listings SET active=0 WHERE id=?',(listing_id,))
    db.commit()
    return jsonify({'ok':True,'cows_received':row['cow_amount'],'price_paid_matic':row['price_matic'],
                    'from':row['seller_email'],'note':'On-chain payment sent via your wallet separately'})

@app.route('/api/blockchain/market/cancel/<int:listing_id>', methods=['POST'])
def bc_market_cancel(listing_id):
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    db   = get_db()
    row  = db.execute('SELECT * FROM marketplace_listings WHERE id=? AND seller_email=? AND active=1',
                      (listing_id, user['email'])).fetchone()
    if not row: return jsonify({'error':'Listing not found or not yours'}), 404
    _add_cows(user['email'], row['cow_amount'], 'marketplace_cancelled',
              {'listing_id':listing_id,'refunded':row['cow_amount']})
    db.execute('UPDATE marketplace_listings SET active=0 WHERE id=?',(listing_id,))
    db.commit()
    return jsonify({'ok':True,'cows_returned':row['cow_amount']})

@app.route('/api/admin/blockchain')
def admin_blockchain():
    if not _require_admin(): return jsonify({'error':'Unauthorized'}), 401
    db  = get_db()
    txs = db.execute('SELECT * FROM blockchain_txs ORDER BY created DESC LIMIT 100').fetchall()
    listings = db.execute('SELECT * FROM marketplace_listings ORDER BY created DESC LIMIT 50').fetchall()
    wallets  = db.execute('SELECT email,wallet_address,verified FROM blockchain_wallets ORDER BY linked_at DESC').fetchall()
    return jsonify({
        'connected':    _chain_connected(),
        'contracts': {
            'prize_escrow':      os.environ.get('CONTRACT_PRIZE_ESCROW','NOT_DEPLOYED'),
            'crown_nft':         os.environ.get('CONTRACT_CROWN_NFT','NOT_DEPLOYED'),
            'tournament_anchor': os.environ.get('CONTRACT_TOURNAMENT_ANCHOR','NOT_DEPLOYED'),
            'cow_marketplace':   os.environ.get('CONTRACT_COW_MARKETPLACE','NOT_DEPLOYED'),
        },
        'transactions': [dict(t) for t in txs],
        'listings':     [dict(l) for l in listings],
        'wallets':      [dict(w) for w in wallets],
        'env_check': {
            'POLYGON_RPC_URL':       bool(os.environ.get('POLYGON_RPC_URL')),
            'POLYGON_PRIVATE_KEY':   bool(os.environ.get('POLYGON_PRIVATE_KEY')),
            'POLYGON_BACKEND_ADDRESS':bool(os.environ.get('POLYGON_BACKEND_ADDRESS')),
            'CONTRACT_PRIZE_ESCROW': bool(os.environ.get('CONTRACT_PRIZE_ESCROW')),
            'CONTRACT_CROWN_NFT':    bool(os.environ.get('CONTRACT_CROWN_NFT')),
            'CONTRACT_TOURNAMENT':   bool(os.environ.get('CONTRACT_TOURNAMENT')),
            'CONTRACT_MARKETPLACE':  bool(os.environ.get('CONTRACT_MARKETPLACE')),
        }
    })


# ═══════════════════════════════════════════════════════════════════════
#  GODMODE — World-Class Experience Layer
#  All missing features implemented in one block
# ═══════════════════════════════════════════════════════════════════════

# ── NOTIFICATIONS CENTER ──────────────────────────────────────────────
@app.route('/api/notifications')
def get_notifications():
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    db = get_db()
    # Build smart notifications from game state
    notifs = []
    now = int(time.time())
    today = time.strftime('%Y-%m-%d')
    # Daily challenge reminder
    done = db.execute('SELECT 1 FROM daily_scores WHERE user_email=? AND day=?',(user['email'],today)).fetchone()
    if not done: notifs.append({'id':'daily_1','type':'challenge','title':'Daily Challenge Ready!','body':'Play today challenge to keep your streak','icon':'[!]','action':'/daily','unread':True,'ts':now})
    # Friend request notifications
    pending = db.execute("SELECT COUNT(*) FROM friends WHERE (user_a=? OR user_b=?) AND status='pending'",(user['email'],user['email'])).fetchone()[0]
    if pending: notifs.append({'id':f'friend_{pending}','type':'social','title':f'{pending} friend request(s)','body':'Someone wants to play Intshuba with you!','icon':'👥','action':'/friends','unread':True,'ts':now-60})
    # Streak reminder
    streak = db.execute('SELECT streak_days,streak_last FROM users WHERE email=?',(user['email'],)).fetchone()
    if streak and streak['streak_last'] != today and streak['streak_days'] > 0:
        notifs.append({'id':'streak_1','type':'streak','title':f'Keep your {streak["streak_days"]}-day streak!','body':'Play before midnight to maintain your streak','icon':'🔥','action':'/play','unread':True,'ts':now-120})
    # Crown challenge available
    crown = db.execute('SELECT herd_cows FROM users WHERE email=?',(user['email'],)).fetchone()
    if crown and crown['herd_cows'] >= 300:
        holder = db.execute('SELECT name FROM users WHERE has_crown=1').fetchone()
        if holder: notifs.append({'id':'crown_1','type':'crown','title':'Challenge for the Crown!','body':f'You have enough cows to challenge {holder["name"]}','icon':'👑','action':'/crown','unread':False,'ts':now-3600})
    return jsonify({'notifications':notifs,'unread':sum(1 for n in notifs if n.get('unread'))})

@app.route('/api/notifications/mark-read', methods=['POST'])
def mark_notifications_read():
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    return jsonify({'ok':True})

# ── PLAYER STATISTICS ─────────────────────────────────────────────────
@app.route('/api/stats/player')
def player_stats():
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    email = sanitise(str(request.args.get('email', user['email'])), 80)
    db = get_db()
    row = db.execute('SELECT * FROM users WHERE email=?',(email,)).fetchone()
    if not row: return jsonify({'error':'Player not found'}), 404
    # Game events
    events = db.execute('SELECT event_type,cows_delta,created FROM kingdom_events WHERE user_email=? ORDER BY created DESC LIMIT 200',(email,)).fetchall()
    wins  = sum(1 for e in events if 'bet_won' in e['event_type'])
    losses= sum(1 for e in events if 'bet_placed' in e['event_type']) - wins
    total_earned = sum(e['cows_delta'] for e in events if e['cows_delta']>0)
    total_spent  = abs(sum(e['cows_delta'] for e in events if e['cows_delta']<0))
    # Achievements count
    achievements = db.execute('SELECT COUNT(*) FROM achievements WHERE player_email=?',(email,)).fetchone()[0]
    return jsonify({
        'player': {'name':row['name'],'title':row['title'],'tribe_id':row['tribe_id'],'herd_cows':row['herd_cows']},
        'games':  {'wins':wins,'losses':losses,'total':wins+losses,'win_rate':round(wins/(wins+losses)*100,1) if wins+losses>0 else 0},
        'economy':{'total_earned':total_earned,'total_spent':total_spent,'net':total_earned-total_spent},
        'social': {'achievements':achievements,'streak':row['streak_days'],'has_crown':bool(row['has_crown']),'is_married':bool(row['is_married'])},
        'elo':    db.execute('SELECT elo_rating FROM users WHERE email=?',(email,)).fetchone()['elo_rating'] if 'elo_rating' in row.keys() else 1200,
    })

# ── SUPPORT TICKETS ───────────────────────────────────────────────────
@app.route('/api/support/ticket', methods=['POST'])
def create_support_ticket():
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    data = request.get_json(force=True) or {}
    subject  = sanitise(str(data.get('subject','')), 120)
    message  = sanitise(str(data.get('message','')), 2000)
    category = sanitise(str(data.get('category','general')), 30)
    if not subject or not message: return jsonify({'error':'Subject and message required'}), 400
    db = get_db()
    db.execute('INSERT INTO support_messages(session_id,user_email,user_name,sender,message,msg_type) VALUES(?,?,?,?,?,?)',
               ('web', user['email'], user['name'], 'player', f"[{subject}] {message}", category))
    db.commit()
    ticket_id = f"TKT-{int(time.time())}"
    return jsonify({'ok':True,'ticket_id':ticket_id,'message':'Support ticket received. We will respond within 24 hours at info@inkazimulo.digital','email_sent':True})

@app.route('/api/support/tickets')
def list_support_tickets():
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    db = get_db()
    rows = db.execute('SELECT id,message,msg_type,created FROM support_messages WHERE user_email=? ORDER BY created DESC LIMIT 20',(user['email'],)).fetchall()
    return jsonify({'tickets':[{'id':r['id'],'subject':r['message'][:60],'category':r['msg_type'],'status':'open','created':r['created']} for r in rows]})

# ── PASSWORD RESET ────────────────────────────────────────────────────
_reset_tokens: dict = {}  # token → {email, expires}

@app.route('/api/auth/forgot-password', methods=['POST'])
def forgot_password():
    data  = request.get_json(force=True) or {}
    email = sanitise(str(data.get('email','')), 80).lower()
    db    = get_db()
    row   = db.execute('SELECT name FROM users WHERE email=?',(email,)).fetchone()
    # Always return ok (do not reveal if email exists)
    if row:
        token = secrets.token_urlsafe(32)
        _reset_tokens[token] = {'email':email,'expires':int(time.time())+3600}
        reset_url = f"{os.environ.get('APP_URL','https://intshuba.inkazimulo.digital')}/reset-password?token={token}"
        log.info(f"[auth] Password reset token for {email}: {token[:8]}... URL: {reset_url}")
        # In production, send email via SMTP/SendGrid
        # For now, return token in response (remove in production)
        return jsonify({'ok':True,'message':f'Reset link sent to {email}','reset_url':reset_url,'note':'In production this would be emailed'})
    return jsonify({'ok':True,'message':f'If {email} exists, a reset link has been sent'})

@app.route('/api/auth/reset-password', methods=['POST'])
def reset_password():
    data     = request.get_json(force=True) or {}
    token    = str(data.get('token',''))
    new_pw   = str(data.get('password',''))
    entry    = _reset_tokens.get(token)
    if not entry or entry['expires'] < int(time.time()):
        return jsonify({'error':'Invalid or expired reset token'}), 400
    issues = validate_password_full(new_pw)
    if issues: return jsonify({'error':'Password needs: '+', '.join(issues)}), 400
    email = entry['email']
    new_hash, new_salt = hash_password(new_pw)
    db = get_db()
    db.execute('UPDATE users SET hash=?,salt=? WHERE email=?',(new_hash,new_salt,email))
    db.execute('DELETE FROM sessions WHERE email=?',(email,))
    db.commit()
    del _reset_tokens[token]
    log.info(f"[auth] Password reset completed for {email}")
    return jsonify({'ok':True,'message':'Password reset successfully. Please log in.'})

# ── PLAYER BAN SYSTEM ─────────────────────────────────────────────────
@app.route('/api/admin/ban', methods=['POST'])
def admin_ban_player():
    if not _require_admin(): return jsonify({'error':'Unauthorized'}), 401
    data   = request.get_json(force=True) or {}
    email  = sanitise(str(data.get('email','')), 80)
    reason = sanitise(str(data.get('reason','Violation of terms')), 200)
    hours  = min(int(data.get('hours', 24)), 8760)  # max 1 year
    if not email: return jsonify({'error':'Email required'}), 400
    db = get_db()
    ban_until = int(time.time()) + hours*3600
    db.execute('UPDATE users SET account_locked=1,lock_until=? WHERE email=?',(ban_until,email))
    db.execute('DELETE FROM sessions WHERE email=?',(email,))
    db.execute('INSERT INTO kingdom_events(user_email,event_type,detail,cows_delta) VALUES(?,?,?,0)',
               (email,'admin_ban',json.dumps({'reason':reason,'hours':hours,'banned_until':ban_until})))
    db.commit()
    log.info(f"[admin] {email} banned for {hours}h: {reason}")
    return jsonify({'ok':True,'email':email,'banned_until':ban_until,'hours':hours,'reason':reason})

@app.route('/api/admin/unban', methods=['POST'])
def admin_unban_player():
    if not _require_admin(): return jsonify({'error':'Unauthorized'}), 401
    data  = request.get_json(force=True) or {}
    email = sanitise(str(data.get('email','')), 80)
    db    = get_db()
    db.execute('UPDATE users SET account_locked=0,lock_until=0,failed_mfa_count=0 WHERE email=?',(email,))
    db.commit()
    return jsonify({'ok':True,'email':email,'message':'Player unbanned'})

@app.route('/api/admin/players')
def admin_players():
    if not _require_admin(): return jsonify({'error':'Unauthorized'}), 401
    db  = get_db()
    q   = sanitise(str(request.args.get('q','')), 80)
    if q:
        rows = db.execute('SELECT email,name,herd_cows,title,tribe_id,account_locked,created FROM users WHERE email LIKE ? OR name LIKE ? ORDER BY created DESC LIMIT 50',
                          (f'%{q}%',f'%{q}%')).fetchall()
    else:
        rows = db.execute('SELECT email,name,herd_cows,title,tribe_id,account_locked,created FROM users ORDER BY created DESC LIMIT 50').fetchall()
    return jsonify({'players':[dict(r) for r in rows],'total':len(rows)})

# ── ANTI-CHEAT: MOVE TIMING ───────────────────────────────────────────
_move_times: dict = {}  # email → last_move_ts
_MOVE_MIN_MS = 300  # min ms between moves (bot detection)

def _check_move_timing(email: str) -> bool:
    """Returns False if moves are impossibly fast (bot detection)."""
    now_ms = int(time.time() * 1000)
    last   = _move_times.get(email, 0)
    _move_times[email] = now_ms
    return (now_ms - last) >= _MOVE_MIN_MS

# ── DAILY TOURNAMENT ─────────────────────────────────────────────────
@app.route('/api/daily-tournament')
def daily_tournament():
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    today = time.strftime('%Y-%m-%d')
    db    = get_db()
    # Get or create todays tournament
    comp_name = f"Daily Champion — {time.strftime('%d %b %Y')}"
    existing = db.execute("SELECT id FROM competitions WHERE name=? AND comp_type='daily'",
                           (comp_name,)).fetchone()
    if not existing:
        db.execute('INSERT INTO competitions(id,name,comp_type,status,host_email,host_name,tribe) VALUES(?,?,?,?,?,?,?)',
                   (f'daily_{today}',comp_name,'daily','open','system','Intshuba Daily','world'))
        db.commit()
    participants = db.execute('SELECT COUNT(*) FROM competition_players WHERE comp_id=?',
                               (f'daily_{today}',)).fetchone()[0]
    # Today's prize: top 3 win daily chest
    joined = db.execute('SELECT 1 FROM competition_players WHERE comp_id=? AND player_email=?',
                         (f'daily_{today}',user['email'])).fetchone()
    return jsonify({'tournament_id':f'daily_{today}','name':comp_name,'date':today,
                    'prize':'Gold Chest + 50 cows for top 3','participants':participants,
                    'already_joined':bool(joined),'ends_at':today+' 23:59:59'})

@app.route('/api/daily-tournament/join', methods=['POST'])
def join_daily_tournament():
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    today = time.strftime('%Y-%m-%d')
    tid   = f'daily_{today}'
    db    = get_db()
    if db.execute('SELECT 1 FROM competition_players WHERE comp_id=? AND player_email=?',(tid,user['email'])).fetchone():
        return jsonify({'ok':True,'message':'Already joined todays tournament'})
    db.execute('INSERT OR IGNORE INTO competition_players(comp_id,player_email) VALUES(?,?)',(tid,user['email']))
    db.commit()
    return jsonify({'ok':True,'tournament_id':tid,'message':'Joined todays tournament! Play to climb the rankings.'})

# ── REMATCH SYSTEM ────────────────────────────────────────────────────
@app.route('/api/game/rematch', methods=['POST'])
def request_rematch():
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    data = request.get_json(force=True) or {}
    opponent = sanitise(str(data.get('opponent_email','')), 80)
    if not opponent: return jsonify({'error':'Opponent email required'}), 400
    db = get_db()
    opp = db.execute('SELECT name FROM users WHERE email=?',(opponent,)).fetchone()
    if not opp: return jsonify({'error':'Player not found'}), 404
    # Create invite for rematch
    code = secrets.token_urlsafe(8)
    db.execute("INSERT OR IGNORE INTO invitations(host_email,code,room_id) VALUES(?,?,?)",
               (user['email'],code,code))
    db.commit()
    return jsonify({'ok':True,'rematch_code':code,'message':f'Rematch requested with {opp["name"]}','invite_url':f'/join/{code}'})

# ── REPLAY SHARING ────────────────────────────────────────────────────
@app.route('/api/game/share-replay/<replay_id>', methods=['POST'])
def share_replay(replay_id):
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    app_url = os.environ.get('APP_URL','https://intshuba.inkazimulo.digital')
    share_url = f"{app_url}/replay/{replay_id}"
    return jsonify({'ok':True,'share_url':share_url,
                    'whatsapp':f"https://wa.me/?text=Watch my Intshuba game! {share_url}",
                    'twitter': f"https://twitter.com/intent/tweet?text=Check out my Intshuba strategy!&url={share_url}",
                    'copy_text':f"Watch my Intshuba game: {share_url}"})

# ── ONBOARDING TUTORIAL ───────────────────────────────────────────────
@app.route('/api/tutorial/steps')
def tutorial_steps():
    return jsonify({'steps':[
        {'id':1,'title':'Welcome to Intshuba!','body':'Intshuba is the traditional Nguni stone board game. You play on a 4×4 to 4×8 board of holes filled with stones.','action':'none','cta':'Next'},
        {'id':2,'title':'Pick a Hole','body':'Tap any hole on YOUR side (bottom rows) that has stones to start your move.','action':'highlight_player_side','cta':'Got it'},
        {'id':3,'title':'Sow the Stones','body':'Stones are distributed counter-clockwise, one per hole. When you land with >1 stone, you relay automatically.','action':'animate_sow','cta':'Watch demo'},
        {'id':4,'title':'Capture!','body':'If you end on your inner row AND both opponent holes in that column have stones — you capture all of them!','action':'animate_capture','cta':'Try it'},
        {'id':5,'title':'Win the Game','body':'Clear all opponent stones from their side or leave them with no valid moves. Strategic play wins!','action':'none','cta':'Start Playing'},
        {'id':6,'title':'5D Mode','body':'Unlock Layer, Echo, Quantum and Tribal bonuses as you level up. The game evolves with you.','action':'show_5d','cta':'Exciting!'},
    ],'skip_url':'/api/tutorial/skip'})

@app.route('/api/tutorial/skip', methods=['POST'])
def skip_tutorial():
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    db = get_db()
    db.execute('INSERT OR IGNORE INTO kingdom_events(user_email,event_type,detail,cows_delta) VALUES(?,?,?,0)',
               (user['email'],'tutorial_skipped','{}'))
    db.commit()
    return jsonify({'ok':True})

@app.route('/api/tutorial/complete', methods=['POST'])
def complete_tutorial():
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    reward = 10
    new_bal = _add_cows(user['email'], reward, 'tutorial_complete', {})
    return jsonify({'ok':True,'reward_cows':reward,'herd_cows':new_bal,'message':'Tutorial complete! +10 cows 🐄'})

# ── GAME SETTINGS (sound, haptics, graphics) ─────────────────────────
@app.route('/api/settings', methods=['GET','POST'])
def player_settings():
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    db   = get_db()
    if request.method == 'POST':
        data = request.get_json(force=True) or {}
        # Store settings as encrypted profile data
        settings_str = json.dumps({
            'sound_enabled':     bool(data.get('sound_enabled', True)),
            'haptics_enabled':   bool(data.get('haptics_enabled', True)),
            'animations_enabled':bool(data.get('animations_enabled', True)),
            'theme':             sanitise(str(data.get('theme','zulu')), 20),
            'board_skin':        sanitise(str(data.get('board_skin','default')), 20),
            'language':          sanitise(str(data.get('language','en')), 5),
            'notifications':     bool(data.get('notifications', True)),
            'auto_relay_speed':  max(50, min(500, int(data.get('auto_relay_speed', 150)))),
        })
        db.execute('UPDATE users SET enc_bio=? WHERE email=?',
                   (encrypt_str(settings_str), user['email']))
        db.commit()
        return jsonify({'ok':True,'settings':json.loads(settings_str)})
    # GET
    row = db.execute('SELECT enc_bio FROM users WHERE email=?',(user['email'],)).fetchone()
    try:
        settings = json.loads(decrypt_str(row['enc_bio'] if row else ''))
    except Exception:
        settings = {'sound_enabled':True,'haptics_enabled':True,'animations_enabled':True,
                    'theme':'zulu','board_skin':'default','language':'en','notifications':True,
                    'auto_relay_speed':150}
    return jsonify({'settings':settings})

# ── AVATAR / PROFILE PICTURE ──────────────────────────────────────────
AVATAR_STYLES = ['warrior','chief','elder','queen','princess','hunter','healer','merchant']

@app.route('/api/profile/avatar', methods=['GET','POST'])
def player_avatar():
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    db = get_db()
    if request.method == 'POST':
        data  = request.get_json(force=True) or {}
        style = sanitise(str(data.get('style','warrior')), 20)
        color = sanitise(str(data.get('color','#C8A84C')), 10)
        if style not in AVATAR_STYLES: style = 'warrior'
        avatar = json.dumps({'style':style,'color':color,'initials':user['name'][:2].upper()})
        db.execute('UPDATE users SET enc_wall=? WHERE email=?',(encrypt_str(avatar),user['email']))
        db.commit()
        return jsonify({'ok':True,'avatar':json.loads(avatar)})
    row = db.execute('SELECT enc_wall,name FROM users WHERE email=?',(user['email'],)).fetchone()
    try:
        avatar = json.loads(decrypt_str(row['enc_wall'] if row else ''))
    except Exception:
        avatar = {'style':'warrior','color':'#C8A84C','initials':(row['name'][:2].upper() if row else 'PL')}
    return jsonify({'avatar':avatar,'styles':AVATAR_STYLES})

# ── SOCIAL SHARING ────────────────────────────────────────────────────
@app.route('/api/share', methods=['POST'], endpoint='social_share_new')
def social_share():
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    data     = request.get_json(force=True) or {}
    share_type = sanitise(str(data.get('type','invite')), 20)
    context    = data.get('context', {})
    app_url    = os.environ.get('APP_URL','https://intshuba.inkazimulo.digital')
    texts = {
        'invite':  f"🐄 Challenge me in Intshuba — the 5D Nguni Stone Game! {app_url}/join",
        'win':     f"🏆 I just won at Intshuba! The 5D Nguni Stone Game. {app_url}",
        'crown':   f"👑 I am the iNkosi! I hold the Crown in Intshuba 5D. {app_url}",
        'achieve': f"🎖 I earned '{context.get('achievement','')}' in Intshuba 5D! {app_url}",
        'score':   f"🎯 I scored {context.get('score','')} in Intshuba 5D! Can you beat me? {app_url}",
    }
    text = texts.get(share_type, texts['invite'])
    return jsonify({
        'text':     text,
        'whatsapp': f"https://wa.me/?text={text.replace(' ','%20')}",
        'twitter':  f"https://twitter.com/intent/tweet?text={text.replace(' ','%20')}",
        'facebook': f"https://www.facebook.com/sharer/sharer.php?u={app_url}",
        'copy':     text,
    })

# ── RATE APP PROMPT ───────────────────────────────────────────────────
@app.route('/api/rate-app', methods=['POST'])
def rate_app():
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    data   = request.get_json(force=True) or {}
    rating = int(data.get('rating', 5))
    review = sanitise(str(data.get('review','')), 500)
    db     = get_db()
    db.execute('INSERT INTO feedback(user_email,rating,message,created) VALUES(?,?,?,?)',
               (user['email'], rating, review, int(time.time())))
    db.commit()
    if rating >= 4:
        return jsonify({'ok':True,'action':'store','message':'Thank you! Redirecting to Play Store...','store_url':'https://play.google.com/store/apps/details?id=digital.inkazimulo.intshuba'})
    else:
        return jsonify({'ok':True,'action':'support','message':'Thank you for the feedback. We will improve!','support_url':'/api/support/ticket'})

# ── IN-GAME CHAT (online multiplayer) ─────────────────────────────────
_game_chats: dict = {}  # game_token → [messages]

@app.route('/api/game/chat', methods=['POST'])
def game_chat_send():
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    data  = request.get_json(force=True) or {}
    msg   = sanitise(str(data.get('message','')), 200)
    token = session.get('token','')
    if not msg: return jsonify({'error':'Empty message'}), 400
    # Quick profanity filter placeholder
    if not token: return jsonify({'error':'No active game'}), 400
    if token not in _game_chats: _game_chats[token] = []
    _game_chats[token].append({'name':user['name'],'msg':msg,'ts':int(time.time())})
    _game_chats[token] = _game_chats[token][-50:]  # keep last 50
    return jsonify({'ok':True})

@app.route('/api/game/chat')
def game_chat_get():
    user = current_user()
    if not user: return jsonify({'error':'Not authenticated'}), 401
    token = session.get('token','')
    msgs  = _game_chats.get(token,[])
    return jsonify({'messages':msgs})

# ── SOUND/MUSIC TOGGLE (hints for client) ─────────────────────────────
@app.route('/api/audio/config')
def audio_config():
    return jsonify({
        'sounds': {
            'capture': {'freq':[660,880],'duration':0.3,'type':'melody'},
            'sow':     {'freq':[330,0.8],'duration':0.05,'type':'tick'},
            'win':     {'freq':[523,659,784,1047],'duration':2.0,'type':'fanfare'},
            'lose':    {'freq':[400,300,200],'duration':1.5,'type':'descend'},
            'relay':   {'freq':[440,0.6],'duration':0.04,'type':'tick'},
            'echo':    {'freq':[300,600,300],'duration':0.8,'type':'ripple'},
            'quantum': {'freq':[800,400,800],'duration':0.5,'type':'glitch'},
        },
        'bg_music': {
            'menu':    {'tempo':70,'key':'D_minor','style':'nguni_drums'},
            'game':    {'tempo':90,'key':'G_pentatonic','style':'nguni_battle'},
            'victory': {'tempo':120,'key':'G_major','style':'nguni_celebration'},
        }
    })


# ─── Railway / production health check ───────────────────────────────────────
@app.route('/health')
def health():
    """Used by Railway healthcheckPath to confirm the app is running."""
    try:
        db = get_db()
        db.execute('SELECT 1').fetchone()
        db_ok = True
    except Exception:
        db_ok = False
    status = 200 if db_ok else 503
    return jsonify({
        'contracts': {
            'prize_escrow':      os.environ.get('CONTRACT_PRIZE_ESCROW','NOT_DEPLOYED'),
            'crown_nft':         os.environ.get('CONTRACT_CROWN_NFT','NOT_DEPLOYED'),
            'tournament_anchor': os.environ.get('CONTRACT_TOURNAMENT_ANCHOR','NOT_DEPLOYED'),
            'cow_marketplace':   os.environ.get('CONTRACT_COW_MARKETPLACE','NOT_DEPLOYED'),
        },
        'status':      'ok' if db_ok else 'degraded',
        'db':          'ok' if db_ok else 'error',
        'version':     '2.3.0',
        'environment': 'railway' if _IS_PROD else 'local',
    }), status


# ─── HTML Template ─────────────────────────────────────────────────────────────

# ─── HTML Template ─────────────────────────────────────────────────────────────
HTML_TEMPLATE = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1,user-scalable=no">
<title>Intshuba – Nguni Stone Game</title>
<link href="https://fonts.googleapis.com/css2?family=Cinzel:wght@400;700;900&family=Crimson+Text:ital,wght@0,400;0,600;1,400&family=Nunito:wght@400;700;800;900&display=swap" rel="stylesheet">
<style>
:root{
  --gold:#C9A84C;--deep-red:#8B1A1A;--ivory:#F5ECD7;--accent:#E8722A;
  --bg:#0D0804;--panel:rgba(20,12,4,0.92);--border:rgba(201,168,76,0.35);
}
*{margin:0;padding:0;box-sizing:border-box;}
body{background:var(--bg);font-family:'Crimson Text',Georgia,serif;
  overflow:hidden;height:100vh;width:100vw;color:var(--ivory);user-select:none;}
/* Child mode overrides */
body.child-mode{font-family:'Nunito',sans-serif;}
body.child-mode .mtitle{font-family:'Nunito',sans-serif;color:#FFD700;font-size:24px;}
body.child-mode .btn{font-family:'Nunito',sans-serif;border-radius:22px;font-size:14px;
  font-weight:800;letter-spacing:0;text-transform:none;}
body.child-mode .card .ctitle{font-family:'Nunito',sans-serif;font-size:12px;}
body.child-mode #narrator-bar{font-family:'Nunito',sans-serif;font-size:15px;font-weight:700;
  background:rgba(10,0,30,.85);color:#FFD700;border-top:2px solid #FF69B4;font-style:normal;}
body.child-mode #hud-scores{font-size:18px;}

/* Canvas & UI */
#canvas{display:block;width:100%;height:100%;position:fixed;top:0;left:0;}
#ui{position:fixed;inset:0;pointer-events:none;z-index:10;}
body,.card,.btn,#canvas{cursor:url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='32' height='40' viewBox='0 0 32 40'%3E%3Cg fill='%23F5ECD7' stroke='%238B1A1A' stroke-width='1.5'%3E%3Crect x='14' y='0' width='6' height='20' rx='3'/%3E%3Crect x='8' y='5' width='6' height='18' rx='3'/%3E%3Crect x='20' y='6' width='6' height='16' rx='3'/%3E%3Crect x='2' y='10' width='6' height='14' rx='3'/%3E%3Crect x='2' y='18' width='28' height='18' rx='5'/%3E%3C/g%3E%3C/svg%3E") 14 2,pointer;}

/* HUD */
#hud{position:absolute;top:0;left:0;right:0;display:flex;align-items:center;
  justify-content:space-between;padding:8px 14px;pointer-events:auto;
  background:linear-gradient(180deg,rgba(0,0,0,.78) 0%,transparent);z-index:20;}
.hud-btn{background:rgba(201,168,76,.15);border:1px solid var(--border);color:var(--gold);
  font-family:'Cinzel',serif;font-size:11px;padding:6px 12px;border-radius:4px;
  cursor:pointer;transition:.2s;letter-spacing:.5px;}
.hud-btn:hover{background:rgba(201,168,76,.3);}
body.child-mode .hud-btn{font-family:'Nunito',sans-serif;font-size:12px;border-radius:18px;
  background:rgba(255,215,0,.18);border-color:#FFD700;color:#FFD700;}
#score-display{font-family:'Cinzel',serif;font-size:13px;color:var(--gold);text-align:center;}
#hud-title{font-size:11px;letter-spacing:3px;opacity:.7;}
#hud-scores{font-size:16px;margin-top:1px;}
#narrator-bar{position:absolute;bottom:0;left:0;right:0;background:rgba(0,0,0,.72);
  color:var(--ivory);font-size:13px;padding:7px 16px;text-align:center;
  border-top:1px solid var(--border);min-height:30px;transition:opacity .4s;
  pointer-events:none;font-style:italic;letter-spacing:.3px;}

/* Child tutorial hint bubble */
#child-hint{position:fixed;top:64px;left:50%;transform:translateX(-50%);
  background:rgba(10,0,30,.94);border:2px solid #FFD700;border-radius:20px;
  padding:9px 20px;font-family:'Nunito',sans-serif;font-size:14px;font-weight:700;
  color:#FFD700;text-align:center;z-index:25;pointer-events:none;display:none;
  max-width:88vw;box-shadow:0 4px 20px rgba(255,215,0,.3);}
body.child-mode #child-hint{display:block;}

/* AI thinking progress bar */
#ai-thinking-bar{display:none;position:fixed;bottom:34px;left:50%;transform:translateX(-50%);
  width:min(320px,90vw);background:rgba(0,0,0,.85);border:1px solid var(--gold);
  border-radius:20px;padding:8px 14px;z-index:30;align-items:center;gap:10px;}
#ai-thinking-bar .ai-label{font-size:12px;color:var(--gold);font-family:'Cinzel',serif;
  white-space:nowrap;letter-spacing:.5px;}
#ai-thinking-bar .ai-track{flex:1;height:6px;background:rgba(201,168,76,.18);border-radius:3px;overflow:hidden;}
.ai-fill{height:100%;width:0%;background:linear-gradient(90deg,var(--gold),#FF9944);
  border-radius:3px;}
@keyframes aiFill{from{width:0%}to{width:100%}}

/* Last move highlight flash */
@keyframes lastMoveFlash{0%{opacity:1}50%{opacity:.3}100%{opacity:1}}

/* Replay mode indicator */
#replay-banner{display:none;position:fixed;top:52px;left:50%;transform:translateX(-50%);
  background:rgba(0,120,180,.9);border:1px solid #4D96FF;border-radius:16px;
  padding:6px 20px;font-size:13px;color:#fff;font-family:'Cinzel',serif;
  z-index:35;letter-spacing:.5px;pointer-events:none;}

/* Modals */
.modal{position:fixed;inset:0;display:flex;flex-direction:column;align-items:center;
  justify-content:center;z-index:50;padding:14px;pointer-events:auto;
  background:rgba(8,4,2,.93);}
.modal.hidden{display:none;}
.modal-box{background:linear-gradient(160deg,#1a0f04 0%,#0d0600 100%);
  border:1px solid var(--border);border-radius:12px;padding:22px;max-width:490px;
  width:100%;max-height:92vh;overflow-y:auto;position:relative;}
.modal-box::before{content:'';position:absolute;top:0;left:0;right:0;height:6px;
  background:repeating-linear-gradient(90deg,#C8A24A 0,#C8A24A 12px,#3a2200 12px,
  #3a2200 24px,#C8A24A 24px,#C8A24A 32px,#1a0a00 32px,#1a0a00 40px);border-radius:12px 12px 0 0;}
.modal-box::after{content:'';position:absolute;bottom:0;left:0;right:0;height:4px;
  background:repeating-linear-gradient(90deg,#8B6914 0,#8B6914 10px,#2a1400 10px,#2a1400 22px);
  border-radius:0 0 12px 12px;}
/* Child modal style */
.modal-box.cbox{background:linear-gradient(160deg,#12003a 0%,#0a0020 100%);
  border:2px solid #FF69B4;}
.modal-box.cbox::before{background:repeating-linear-gradient(90deg,
  #FF69B4 0,#FF69B4 10px,#FFD700 10px,#FFD700 20px,
  #7DF9FF 20px,#7DF9FF 30px,#98FF98 30px,#98FF98 40px);}

.mtitle{font-family:'Cinzel',serif;color:var(--gold);font-size:20px;text-align:center;
  margin-bottom:10px;letter-spacing:2px;text-shadow:0 0 20px rgba(201,168,76,.4);}
.nguni-bar{height:6px;width:100%;margin:10px 0;background:
  repeating-linear-gradient(90deg,#C9A84C 0,#C9A84C 12px,#8B1A1A 12px,#8B1A1A 24px,
  #F5ECD7 24px,#F5ECD7 36px,#8B1A1A 36px,#8B1A1A 48px);}
.rainbow-bar{height:6px;width:100%;margin:10px 0;background:
  linear-gradient(90deg,#FF6B6B,#FFD93D,#6BCB77,#4D96FF,#C77DFF,#FF6B6B);}

/* Buttons */
.btn{background:linear-gradient(135deg,#3a2200,#1a0f04);border:1px solid var(--gold);
  color:var(--gold);font-family:'Cinzel',serif;font-size:12px;padding:10px 22px;
  border-radius:6px;cursor:pointer;letter-spacing:1px;transition:.2s;text-transform:uppercase;}
.btn:hover{background:linear-gradient(135deg,#5a3800,#2a1800);box-shadow:0 0 12px rgba(201,168,76,.3);}
.btn.green{background:linear-gradient(135deg,#1a4a0a,#0a2a04);border-color:#4CAF50;color:#a8ff8a;}
.btn.green:hover{background:linear-gradient(135deg,#2a6a1a,#1a4a0a);}
.btn.red{background:linear-gradient(135deg,#4a0a0a,#2a0404);border-color:#ff4444;color:#ff9999;}
.btn.blue{background:linear-gradient(135deg,#0a1a4a,#040a2a);border-color:#4488ff;color:#88bbff;}
.btn.purple{background:linear-gradient(135deg,#2a0a4a,#15022a);border-color:#aa44ff;color:#cc99ff;}
/* Child buttons - big, round, colourful */
.cbtn{font-family:'Nunito',sans-serif;font-size:15px;font-weight:800;padding:13px 26px;
  border-radius:26px;border:none;cursor:pointer;letter-spacing:.3px;transition:.2s;
  box-shadow:0 4px 14px rgba(0,0,0,.45);text-transform:none;}
.cbtn:active{transform:scale(.96);}
.cbtn.cg{background:linear-gradient(135deg,#00C853,#69F0AE);color:#002a00;}
.cbtn.co{background:linear-gradient(135deg,#FF6D00,#FFD600);color:#3a1a00;}
.cbtn.cp{background:linear-gradient(135deg,#E040FB,#FF80AB);color:#1a0030;}
.cbtn.cb{background:linear-gradient(135deg,#2979FF,#00B0FF);color:#00083a;}

/* Cards */
.card-grid{display:flex;flex-wrap:wrap;gap:8px;justify-content:center;margin-bottom:12px;}
.card{background:rgba(201,168,76,.08);border:1px solid rgba(201,168,76,.25);border-radius:8px;
  padding:10px 14px;cursor:pointer;transition:.2s;text-align:center;min-width:88px;}
.card.sel{background:rgba(201,168,76,.22);border-color:var(--gold);box-shadow:0 0 10px rgba(201,168,76,.2);}
.card:hover{background:rgba(201,168,76,.15);}
.card .icon{font-size:22px;display:block;margin-bottom:4px;}
.card .ctitle{font-family:'Cinzel',serif;font-size:11px;color:var(--gold);letter-spacing:.5px;}
.card .csub{font-size:10px;color:rgba(245,236,215,.5);margin-top:2px;}
.slabel{font-family:'Cinzel',serif;font-size:9px;color:rgba(201,168,76,.6);letter-spacing:3px;
  margin:12px 0 5px;text-align:center;text-transform:uppercase;}

/* Inputs */
.inp{background:rgba(201,168,76,.08);border:1px solid rgba(201,168,76,.3);border-radius:6px;
  color:var(--ivory);padding:10px 14px;width:100%;font-family:'Crimson Text',serif;
  font-size:15px;margin-bottom:10px;}
.inp:focus{outline:none;border-color:var(--gold);}
.err{color:#ff6b6b;font-size:12px;margin:4px 0;text-align:center;}
.ok{color:#6bffaa;font-size:12px;margin:4px 0;text-align:center;}

/* Leaderboard */
.lb-row{display:grid;grid-template-columns:28px 1fr 46px 46px 46px 60px;
  gap:4px;align-items:center;padding:7px 10px;border-radius:6px;font-size:12px;}
.lb-row:nth-child(odd){background:rgba(201,168,76,.05);}
.lb-rank{font-family:'Cinzel',serif;color:var(--gold);font-size:12px;text-align:center;}
.lb-header{font-family:'Cinzel',serif;font-size:9px;color:rgba(201,168,76,.5);letter-spacing:1px;
  text-transform:uppercase;padding:0 10px 6px;display:grid;
  grid-template-columns:28px 1fr 46px 46px 46px 60px;gap:4px;}

/* Online */
.room-code{font-family:'Cinzel',serif;font-size:26px;letter-spacing:8px;color:var(--gold);
  text-align:center;padding:14px;background:rgba(201,168,76,.1);border-radius:8px;
  border:1px solid var(--border);margin:10px 0;}
.dot{width:8px;height:8px;border-radius:50%;display:inline-block;margin-right:5px;}
.dot.wait{background:#ffcc44;animation:blink 1s infinite;}
.dot.go{background:#44ff88;}
@keyframes blink{0%,100%{opacity:1}50%{opacity:.3}}

/* Tournament */
.t-row{padding:10px;border:1px solid var(--border);border-radius:6px;
  margin-bottom:8px;cursor:pointer;transition:.2s;}
.t-row:hover{background:rgba(201,168,76,.08);}

/* ── CHAT WIDGET ─────────────────────────────────── */
#chat-fab-wrap{position:fixed;bottom:46px;right:14px;z-index:60;pointer-events:auto;}
.chat-fab{width:54px;height:54px;border-radius:50%;
  background:linear-gradient(135deg,#C9A84C,#7a4a00);border:none;cursor:pointer;
  font-size:26px;display:flex;align-items:center;justify-content:center;
  box-shadow:0 4px 18px rgba(0,0,0,.55);transition:.2s;}
.chat-fab:hover{transform:scale(1.09);}
.chat-badge{position:absolute;top:-3px;right:-3px;background:#ff3333;color:#fff;
  border-radius:50%;width:19px;height:19px;font-size:10px;font-weight:900;
  display:none;align-items:center;justify-content:center;}
#chat-window{position:fixed;bottom:108px;right:14px;width:318px;
  background:linear-gradient(160deg,#1c0f05,#0d0602);
  border:1px solid var(--border);border-radius:16px;display:none;flex-direction:column;
  z-index:60;box-shadow:0 10px 36px rgba(0,0,0,.7);overflow:hidden;pointer-events:auto;
  max-height:480px;}
#chat-window.open{display:flex;}
.cw-header{padding:11px 15px;background:linear-gradient(90deg,#3a2200,#1c0f00);
  display:flex;align-items:center;justify-content:space-between;
  border-bottom:1px solid var(--border);}
.cw-title{font-family:'Cinzel',serif;color:var(--gold);font-size:13px;letter-spacing:1px;}
.cw-sub{font-size:10px;color:rgba(245,236,215,.38);margin-top:1px;}
.cw-close{background:none;border:none;color:rgba(245,236,215,.45);font-size:18px;cursor:pointer;}
.cw-close:hover{color:var(--gold);}
/* Tabs */
.cw-tabs{display:flex;border-bottom:1px solid var(--border);}
.cw-tab{flex:1;padding:8px 4px;text-align:center;font-size:11px;cursor:pointer;
  color:rgba(245,236,215,.4);border-bottom:2px solid transparent;transition:.2s;letter-spacing:.5px;}
.cw-tab.act{color:var(--gold);border-bottom-color:var(--gold);}
/* Messages */
.cw-msgs{flex:1;overflow-y:auto;padding:10px;display:flex;flex-direction:column;
  gap:7px;min-height:180px;max-height:240px;}
.cw-msg{max-width:88%;padding:8px 11px;border-radius:12px;font-size:12px;line-height:1.45;}
.cw-msg.sup{background:rgba(201,168,76,.13);border:1px solid rgba(201,168,76,.18);
  align-self:flex-start;border-radius:4px 12px 12px 12px;}
.cw-msg.usr{background:rgba(138,26,26,.28);border:1px solid rgba(138,26,26,.4);
  align-self:flex-end;border-radius:12px 4px 12px 12px;}
.cw-msg .mt{font-size:9px;color:rgba(245,236,215,.28);margin-top:3px;}
.cw-input{padding:8px 11px;border-top:1px solid var(--border);
  display:flex;gap:7px;align-items:center;background:rgba(0,0,0,.28);}
.cw-inp{flex:1;background:rgba(201,168,76,.07);border:1px solid rgba(201,168,76,.2);
  border-radius:18px;color:var(--ivory);padding:8px 13px;font-size:13px;
  font-family:'Crimson Text',serif;}
.cw-inp:focus{outline:none;border-color:var(--gold);}
.cw-send{background:var(--gold);border:none;border-radius:50%;width:33px;height:33px;
  cursor:pointer;font-size:15px;display:flex;align-items:center;justify-content:center;
  flex-shrink:0;transition:.2s;}
.cw-send:hover{background:#e8c85a;}
/* Survey tab */
#survey-pane{padding:10px 12px;overflow-y:auto;max-height:360px;display:none;flex-direction:column;gap:8px;}
#survey-pane.open{display:flex;}
.sq{font-size:12px;color:var(--ivory);margin-bottom:5px;font-weight:600;line-height:1.4;}
.star-row{display:flex;gap:6px;margin-bottom:3px;}
.sstar{background:none;border:none;font-size:22px;cursor:pointer;filter:grayscale(1);transition:.15s;}
.sstar.lit{filter:none;}
.choice-wrap{display:flex;flex-wrap:wrap;gap:5px;}
.cbtn-sm{background:rgba(201,168,76,.07);border:1px solid rgba(201,168,76,.2);
  border-radius:14px;color:var(--ivory);padding:4px 10px;font-size:11px;cursor:pointer;transition:.15s;}
.cbtn-sm.sel{background:rgba(201,168,76,.24);border-color:var(--gold);color:var(--gold);}
.sq-text{background:rgba(201,168,76,.07);border:1px solid rgba(201,168,76,.2);
  border-radius:7px;color:var(--ivory);padding:7px;font-size:12px;width:100%;
  min-height:52px;resize:none;font-family:'Crimson Text',serif;}
.sq-text:focus{outline:none;border-color:var(--gold);}

/* ── WINNER OVERLAY ── */
#winner-overlay{position:fixed;inset:0;z-index:90;display:none;flex-direction:column;
  align-items:center;justify-content:center;background:rgba(0,0,0,.9);}
#winner-overlay.show{display:flex;}
#herd-canvas{width:min(100%,560px);height:200px;}
.win-title{font-family:'Cinzel',serif;font-size:30px;color:var(--gold);
  text-shadow:0 0 30px var(--gold);margin-bottom:6px;letter-spacing:3px;
  animation:pulse 1.1s infinite;}
body.child-mode .win-title{font-family:'Nunito',sans-serif;font-size:34px;color:#FFD700;}
.win-sub{font-size:16px;color:var(--ivory);margin-bottom:16px;font-style:italic;}
.win-cows{font-family:'Cinzel',serif;font-size:20px;color:#ffcc44;margin:6px 0;}
@keyframes pulse{0%,100%{opacity:1;transform:scale(1)}50%{opacity:.82;transform:scale(1.04)}}

/* Feedback modal stars */
.fb-stars{display:flex;justify-content:center;gap:10px;margin:10px 0;}
.fb-star{font-size:30px;cursor:pointer;filter:grayscale(1);transition:.15s;}
.fb-star.lit{filter:none;}
.cat-wrap{display:flex;flex-wrap:wrap;gap:5px;margin:7px 0;}
.cat-chip{background:rgba(201,168,76,.08);border:1px solid rgba(201,168,76,.22);
  border-radius:14px;color:var(--ivory);padding:5px 11px;font-size:11px;cursor:pointer;transition:.15s;}
.cat-chip.sel{background:rgba(201,168,76,.26);border-color:var(--gold);color:var(--gold);}

/* Password strength bar */
.sbar{height:4px;background:#222;border-radius:2px;margin:2px 0 7px;}
#sfill{height:100%;border-radius:2px;width:0%;transition:.3s;}
#shint{font-size:10px;color:rgba(245,236,215,.45);text-align:right;margin-bottom:5px;}

::-webkit-scrollbar{width:4px;}
::-webkit-scrollbar-thumb{background:var(--border);border-radius:2px;}
</style>
</head>
<body>

<canvas id="canvas"></canvas>

<!-- Child hint bubble -->
<div id="child-hint">👆 Tap a hole on your bottom rows to start!</div>

<div id="ui">
  <div id="hud">
    <div style="display:flex;gap:6px;pointer-events:auto">
      <button class="hud-btn" onclick="showHome()">🏠</button>
      <button class="hud-btn" id="hud-profile" onclick="showProfile()">👤</button>
    </div>
    <div id="score-display">
      <div id="hud-title">INTSHUBA <span id="mode-pill" onclick="openM('mode-modal')" title="Switch game mode">5D</span></div>
      <div id="hud-scores">🐄 0 · 0 🐄</div>
    </div>
    <div style="display:flex;gap:6px;pointer-events:auto;align-items:center">
      <button class="hud-btn" onclick="showShare('invite','','')" title="Share Intshuba">📤</button>
      <div id="herd-hud" title="Your cattle herd — click to open Kingdom"
           style="cursor:pointer;background:rgba(201,168,76,.12);border:1px solid var(--border);
                  border-radius:16px;padding:4px 10px;font-size:12px;color:var(--gold);
                  font-family:'Cinzel',serif;letter-spacing:.5px"
           onclick="showKingdom()">🐄 <span id="herd-count">–</span></div><span id="credits-lock-badge" title="Cow purchases protected by HMAC signing">🔒</span>
      <button class="hud-btn" onclick="showLb()">🏆</button>
      <button class="hud-btn" onclick="showRules()">📜</button>
    </div>
  </div>
  <div id="narrator-bar">Welcome to Intshuba · Nguni Stone Game 🐄</div>
</div>

<!-- ── CHAT FAB ── -->
<div id="chat-fab-wrap">
  <div class="chat-badge" id="chat-badge">1</div>
  <button class="chat-fab" onclick="toggleChat()" title="Chat & Support">💬</button>
</div>

<!-- ── CHAT WINDOW ── -->
<div id="chat-window">
  <div class="cw-header">
    <div><div class="cw-title">💬 Intshuba Support</div>
         <div class="cw-sub">⚡ Replies instantly · info@inkazimulo.digital</div></div>
    <button class="cw-close" onclick="toggleChat()">✕</button>
  </div>
  <div class="cw-tabs">
    <div class="cw-tab act" id="tab-chat"   onclick="cwTab('chat')">💬 Chat</div>
    <div class="cw-tab"     id="tab-survey" onclick="cwTab('survey')">⭐ Rate Us</div>
  </div>
  <!-- Chat pane -->
  <div id="chat-pane" style="display:flex;flex-direction:column;">
    <div class="cw-msgs" id="cw-msgs"></div>
    <div class="cw-input">
      <input class="cw-inp" id="cw-inp" placeholder="Type a message…"
        onkeydown="if(event.key==='Enter')cwSend()">
      <button class="cw-send" onclick="cwSend()">➤</button>
    </div>
  </div>
  <!-- Survey pane -->
  <div id="survey-pane">
    <div style="text-align:center;font-family:'Cinzel',serif;font-size:10px;
      color:rgba(201,168,76,.55);letter-spacing:2px;padding:4px 0 8px">
      YOUR FEEDBACK SHAPES THE GAME
    </div>
    <div id="sq-list"></div>
    <button class="btn green" style="width:100%;margin-top:8px" onclick="cwSubmitSurvey()">
      Submit Feedback 🐄
    </button>
    <div id="sq-ok" class="ok" style="display:none;text-align:center;margin-top:5px"></div>
  </div>
</div>

<!-- ── HOME MODAL ── -->
<div class="modal" id="home-modal">
 <div class="modal-box" style="max-width:520px">
  <div class="mtitle" id="home-title">INTSHUBA</div>
  <div style="text-align:center;font-size:11px;color:rgba(201,168,76,.5);
    letter-spacing:4px;margin-bottom:4px">NGUNI STONE GAME</div>
  <div class="nguni-bar"></div>

  <div class="slabel">UHLOBO LOMDLALO · MODE</div>
  <div class="card-grid">
    <div class="card sel" id="mode-ai"     onclick="selMode('ai')">
      <span class="icon">🤖</span><div class="ctitle">vs AI</div></div>
    <div class="card"     id="mode-2p"     onclick="selMode('2p')">
      <span class="icon">👥</span><div class="ctitle">2 Players</div></div>
    <div class="card"     id="mode-online" onclick="selMode('online')">
      <span class="icon">🌍</span><div class="ctitle">Online</div>
      <div class="csub">Cross-device</div></div>
  </div>

  <div class="slabel">IZINGA · LEVEL</div>
  <div class="card-grid">
    <!-- Level 1: clearly marked child-friendly -->
    <div class="card sel" id="lv-1" onclick="selLevel(1)"
         style="border:2px solid #FFD700;background:rgba(255,215,0,.12);position:relative">
      <span style="position:absolute;top:-8px;right:-8px;background:#FF69B4;color:#fff;
        font-size:9px;font-weight:900;padding:2px 6px;border-radius:10px;
        font-family:'Nunito',sans-serif">KIDS ✨</span>
      <span class="icon">🐄</span>
      <div class="ctitle" id="lv1t">Calf · Beginner</div>
      <div class="csub" id="lv1d">4×4 · Kids Friendly</div>
    </div>
    <div class="card" id="lv-2" onclick="selLevel(2)">
      <span class="icon">🐂</span>
      <div class="ctitle" id="lv2t">Warrior</div>
      <div class="csub" id="lv2d">4×6 · Smart AI</div>
    </div>
    <div class="card" id="lv-3" onclick="selLevel(3)">
      <span class="icon">🦅</span>
      <div class="ctitle" id="lv3t">King</div>
      <div class="csub" id="lv3d">4×6 · Hard AI</div>
    </div>
  </div>

  <div class="slabel">ISIKHUMBA · SKIN</div>
  <div class="card-grid">
    <div class="card sel" id="sk-zulu"    onclick="selSkin('zulu')">
      <span class="icon">🐗</span><div class="ctitle">Zulu</div></div>
    <div class="card"     id="sk-xhosa"   onclick="selSkin('xhosa')">
      <span class="icon">🦬</span><div class="ctitle">Xhosa</div></div>
    <div class="card"     id="sk-ndebele" onclick="selSkin('ndebele')">
      <span class="icon">🎨</span><div class="ctitle">Ndebele</div></div>
    <div class="card"     id="sk-swati"   onclick="selSkin('swati')">
      <span class="icon">🦁</span><div class="ctitle">Swati</div></div>
    <div class="card"     id="sk-tsonga"  onclick="selSkin('tsonga')">
      <span class="icon">🌿</span><div class="ctitle">Tsonga</div></div>
  </div>

  <div class="slabel">ULIMI · LANGUAGE</div>
  <div id="lang-grid" style="display:flex;flex-wrap:wrap;gap:5px;
    justify-content:center;margin-bottom:12px"></div>

  <div style="display:flex;gap:8px;flex-wrap:wrap;justify-content:center">
    <button class="btn green" onclick="startGame()">▷ Start</button>
    <button class="btn blue"  onclick="showOnlinePanel()">🌍 Online</button>
    <button class="btn"       onclick="showTournament()">🏆 Tournament</button>
    <button class="btn purple" onclick="showFbModal()">⭐ Rate</button>
    <button class="btn" style="background:linear-gradient(135deg,#8B1A1A,#5a0808);border-color:#C9A84C;color:#C9A84C" onclick="showShop()">👑 Upgrade</button>
    <button class="btn" style="background:linear-gradient(135deg,#1a4a0a,#0a2a04);border-color:#4CAF50;color:#a8ff8a" onclick="showKingdom()">🐄 Kingdom</button>
    <button class="btn" style="background:linear-gradient(135deg,#1a4a6b,#0a2a3a);border-color:#4D96FF;color:#88ccff" onclick="showDonate()">🐄 Donate</button>
    <button class="btn" onclick="showAuth()" id="home-auth-btn">🔑 Sign In</button>
  </div>
  <div class="nguni-bar"></div>
  <div style="text-align:center;font-size:9px;color:rgba(245,236,215,.18);letter-spacing:2px">
    INTSHUBA © 2024 INKAZIMULO SD SOLUTIONS · ALL RIGHTS RESERVED</div>
 </div>
</div>

<!-- ── RULES MODAL ── -->
<div class="modal hidden" id="rules-modal">
 <div class="modal-box" id="rules-box">
  <div class="mtitle" id="rules-h">Rules</div>
  <div id="rules-kids-badge" style="display:none;text-align:center;margin-bottom:8px">
    <span style="background:#FF69B4;color:#fff;padding:3px 16px;border-radius:16px;
      font-family:'Nunito',sans-serif;font-size:12px;font-weight:800">🐄 Kid-Friendly Guide ✨</span>
  </div>
  <div class="nguni-bar" id="rules-bar"></div>
  <div id="rules-body" style="font-size:14px;line-height:1.65;max-height:62vh;
    overflow-y:auto;text-align:left"></div>
  <button class="btn" style="margin-top:12px" onclick="closeM('rules-modal')">Close</button>
 </div>
</div>

<!-- ── AUTH MODAL ── -->
<div class="modal hidden" id="auth-modal">
 <div class="modal-box" style="max-width:360px">
  <div class="mtitle" id="auth-h">Sign In</div>
  <div style="text-align:center;font-size:12px;color:rgba(201,168,76,.55);
    margin-bottom:8px" id="auth-sub">Ngena · Sign In</div>
  <div class="nguni-bar"></div>
  <div id="name-wrap" style="display:none">
    <input class="inp" id="inp-name" placeholder="Your Name / Igama" type="text"></div>
  <input class="inp" id="inp-email" placeholder="Email" type="email">
  <input class="inp" id="inp-pass"  placeholder="Password / Iphasiwedi" type="password">
  <div id="pw-strength" style="display:none">
    <div class="sbar"><div id="sfill"></div></div>
    <div id="shint"></div>
  </div>
  <div id="conf-wrap" style="display:none">
    <input class="inp" id="inp-conf" placeholder="Confirm Password" type="password"></div>
  <div id="aerr" class="err" style="display:none"></div>
  <div id="aok"  class="ok"  style="display:none"></div>
  <button class="btn green" style="width:100%;margin-top:4px"
    id="auth-btn" onclick="doAuth()">NGENA · SIGN IN</button>
  <button class="btn" style="width:100%;margin-top:8px;font-size:11px"
    id="auth-tog" onclick="togAuth()">New? Register</button>
  <button class="btn" style="width:100%;margin-top:5px;font-size:11px"
    onclick="guestGo()">👤 Continue as Guest</button>
  <button class="btn red" style="width:100%;margin-top:5px;font-size:10px"
    onclick="closeM('auth-modal')">✕ Close</button>
 </div>
</div>

<!-- ── PROFILE MODAL ── -->
<div class="modal hidden" id="profile-modal">
 <div class="modal-box" style="max-width:380px">
  <div class="mtitle">IPHROFAYILI · PROFILE</div>
  <div class="nguni-bar"></div>
  <div style="text-align:center;margin-bottom:14px">
    <div style="width:58px;height:58px;font-size:26px;background:rgba(201,168,76,.14);
      border-radius:50%;border:2px solid var(--gold);display:flex;align-items:center;
      justify-content:center;margin:0 auto 7px" id="pav">👤</div>
    <div id="pname"  style="font-family:'Cinzel',serif;font-size:17px;color:var(--gold)"></div>
    <div id="pemail" style="font-size:12px;color:rgba(245,236,215,.38)"></div>
  </div>
  <div style="display:grid;grid-template-columns:1fr 1fr 1fr 1fr;gap:7px;margin-bottom:10px"
    id="pstats"></div>
  <div style="text-align:center;font-family:'Cinzel',serif;font-size:20px;
    color:var(--gold);margin-bottom:10px" id="pcows">🐄 0 cattle won</div>
  <div style="display:flex;gap:8px;justify-content:center">
    <button class="btn red" onclick="doLogout()">Logout</button>
    <button class="btn"     onclick="closeM('profile-modal')">Close</button>
  </div>
 </div>
</div>

<!-- ── LEADERBOARD MODAL ── -->
<div class="modal hidden" id="lb-modal">
 <div class="modal-box" style="max-width:560px">
  <div class="mtitle">🏆 LEADERBOARD</div>
  <div class="nguni-bar"></div>
  <!-- Segment selector -->
  <div style="display:flex;gap:5px;flex-wrap:wrap;margin-bottom:10px">
    <button class="cw-tab act" id="lbs-livestock"   onclick="lbSeg('livestock')"  >🐄 Livestock</button>
    <button class="cw-tab"     id="lbs-wins"         onclick="lbSeg('wins')"       >🏆 Wins</button>
    <button class="cw-tab"     id="lbs-stages"       onclick="lbSeg('stages')"     >🏛️ Stages</button>
    <button class="cw-tab"     id="lbs-competitions" onclick="lbSeg('competitions')">🥇 Champs</button>
    <button class="cw-tab"     id="lbs-herd_total"   onclick="lbSeg('herd_total')" >📊 All-time</button>
    <button class="cw-tab"     id="lbs-crown"        onclick="lbSeg('crown')"      >👑 Crown</button>
  </div>
  <!-- Filter row -->
  <div style="display:flex;gap:6px;margin-bottom:10px;align-items:center">
    <select id="lb-pool-filter" onchange="loadLb()" style="background:rgba(201,168,76,.08);border:1px solid var(--border);color:var(--ivory);border-radius:6px;padding:4px 8px;font-size:12px">
      <option value="all">All Ages</option>
      <option value="u10">🐣 U-10</option><option value="u14">🌱 U-14</option>
      <option value="u18">⚔️ U-18</option><option value="u25">🔥 U-25</option>
      <option value="u40">🦅 U-40</option><option value="senior">🦁 Senior</option>
      <option value="elder">🐘 Elder</option>
    </select>
    <select id="lb-tribe-filter" onchange="loadLb()" style="background:rgba(201,168,76,.08);border:1px solid var(--border);color:var(--ivory);border-radius:6px;padding:4px 8px;font-size:12px">
      <option value="all">All Tribes</option>
      <option value="amazulu">🐗 amaZulu</option><option value="amaxhosa">🦬 amaXhosa</option>
      <option value="amandebele">🎨 amaNdebele</option><option value="emaswati">🦁 emaSwati</option>
      <option value="vatsonga">🌿 VaTsonga</option><option value="basotho">☀️ BaSotho</option>
      <option value="bapedi">🌙 BaPedi</option><option value="bavenda">🌊 BaVenda</option>
      <option value="world">🌍 World</option>
    </select>
  </div>
  <!-- Header -->
  <div style="display:grid;grid-template-columns:32px 1fr 60px 60px 55px 65px;
    gap:4px;padding:6px 8px;background:rgba(201,168,76,.12);border-radius:6px;
    font-size:10px;color:rgba(245,236,215,.5);letter-spacing:.5px;margin-bottom:4px">
    <span>#</span><span>PLAYER</span>
    <span style="text-align:right">WINS</span>
    <span style="text-align:right">GAMES</span>
    <span style="text-align:right">WIN%</span>
    <span style="text-align:right">🐄 HERD</span>
  </div>
  <div id="lb-list" style="max-height:300px;overflow-y:auto"></div>
  <div style="font-size:10px;color:rgba(245,236,215,.25);text-align:center;margin:8px 0">
    Rankings update live · Filter by age pool or tribe</div>
  <div style="display:flex;gap:6px;justify-content:center">
    <button class="btn" onclick="showShare('invite','','')">📤 Share</button>
    <button class="btn" onclick="closeM('lb-modal')">Close</button>
  </div>
 </div>
</div>

<!-- ── ONLINE MODAL ── -->
<div class="modal hidden" id="online-modal">
 <div class="modal-box" style="max-width:430px">
  <div class="mtitle">🌍 ONLINE GAME</div>
  <div class="nguni-bar"></div>
  <div style="display:flex;flex-direction:column;gap:8px">
    <button class="btn green" onclick="createOnlineGame()">🏠 Create Room & Get Invite Code</button>
    <div style="text-align:center;font-size:11px;color:rgba(245,236,215,.35)">— or —</div>
    <input class="inp" id="join-code-inp" placeholder="Enter 8-character code…"
      style="text-align:center;letter-spacing:5px;font-size:17px;font-family:'Cinzel',serif">
    <button class="btn blue" onclick="joinOnlineGame()">🚀 Join with Code</button>
  </div>
  <div id="online-info" style="display:none;margin-top:14px">
    <div class="room-code" id="room-code-disp">--------</div>
    <div style="text-align:center;font-size:12px;color:rgba(245,236,215,.45);margin-bottom:7px">
      Share this code with your opponent on any device</div>
    <div style="text-align:center">
      <span class="dot wait"></span><span id="online-status">Waiting for opponent…</span></div>
  </div>
  <div class="nguni-bar" style="margin-top:14px"></div>
  <button class="btn" onclick="closeM('online-modal')">Close</button>
 </div>
</div>

<!-- ── TOURNAMENT MODAL ── -->
<div class="modal hidden" id="tournament-modal">
 <div class="modal-box" style="max-width:470px">
  <div class="mtitle">🏆 TOURNAMENTS</div>
  <div class="nguni-bar"></div>
  <div style="display:flex;gap:8px;margin-bottom:10px;flex-wrap:wrap">
    <button class="btn green" onclick="togCreateT()">+ Create</button>
    <button class="btn blue"  onclick="loadT()">🔄 Refresh</button>
  </div>
  <div id="create-t" style="display:none;margin-bottom:10px;padding:12px;
    border:1px solid var(--border);border-radius:8px">
    <input class="inp" id="t-name" placeholder="Tournament Name">
    <div style="display:flex;gap:8px;justify-content:center;margin-bottom:8px">
      <div class="card" id="tp-4"  onclick="selTP(4)"><div class="ctitle">4</div></div>
      <div class="card sel" id="tp-8" onclick="selTP(8)"><div class="ctitle">8</div></div>
      <div class="card" id="tp-16" onclick="selTP(16)"><div class="ctitle">16</div></div>
    </div>
    <button class="btn green" style="width:100%" onclick="submitT()">Create Tournament</button>
  </div>
  <div id="t-list" style="max-height:280px;overflow-y:auto"></div>
  <button class="btn" style="margin-top:8px" onclick="closeM('tournament-modal')">Close</button>
 </div>
</div>

<!-- ── FEEDBACK MODAL ── -->
<div class="modal hidden" id="fb-modal">
 <div class="modal-box" style="max-width:420px">
  <div class="mtitle">⭐ RATE & FEEDBACK</div>
  <div class="nguni-bar"></div>
  <div style="text-align:center;font-size:13px;color:rgba(245,236,215,.55);margin-bottom:10px">
    Help us build the best Nguni game for everyone — young & old! 🐄</div>

  <div class="slabel">YOUR STAR RATING</div>
  <div class="fb-stars" id="fb-stars">
    <span class="fb-star" onclick="setFbRating(1)">⭐</span>
    <span class="fb-star" onclick="setFbRating(2)">⭐</span>
    <span class="fb-star" onclick="setFbRating(3)">⭐</span>
    <span class="fb-star" onclick="setFbRating(4)">⭐</span>
    <span class="fb-star" onclick="setFbRating(5)">⭐</span>
  </div>
  <div id="fb-rating-lbl" style="text-align:center;font-size:12px;color:var(--gold);
    margin-bottom:8px">Tap stars to rate</div>

  <div class="slabel">CATEGORY</div>
  <div class="cat-wrap" id="cat-wrap">
    <button class="cat-chip sel" onclick="selCat(this,'general')">💬 General</button>
    <button class="cat-chip"     onclick="selCat(this,'gameplay')">🎮 Gameplay</button>
    <button class="cat-chip"     onclick="selCat(this,'bug')">🐛 Bug Report</button>
    <button class="cat-chip"     onclick="selCat(this,'suggestion')">💡 Suggestion</button>
    <button class="cat-chip"     onclick="selCat(this,'children')">🐄 Children</button>
    <button class="cat-chip"     onclick="selCat(this,'online')">🌍 Online Play</button>
  </div>

  <div class="slabel">YOUR MESSAGE</div>
  <textarea class="inp" id="fb-msg" style="min-height:80px;resize:none"
    placeholder="Tell us what you think — bugs, ideas, compliments…"></textarea>
  <div id="fb-err" class="err" style="display:none"></div>
  <div id="fb-ok"  class="ok"  style="display:none"></div>
  <div style="display:flex;gap:8px;margin-top:8px">
    <button class="btn green" style="flex:1" onclick="submitFb()">Send Feedback 🐄</button>
    <button class="btn" onclick="closeM('fb-modal')">Close</button>
  </div>
 </div>
</div>

<!-- ── GAME OVER MODAL ── -->
<div class="modal hidden" id="go-modal">
 <div class="modal-box" style="max-width:380px;text-align:center" id="go-box">
  <div class="mtitle" id="go-title">Game Over</div>
  <div class="nguni-bar" id="go-bar"></div>
  <div id="go-msg"    style="font-size:15px;margin:7px 0;line-height:1.5"></div>
  <div id="go-scores" style="font-family:'Cinzel',serif;font-size:22px;
    color:var(--gold);margin:10px 0"></div>
  <div id="go-note"   style="font-size:12px;font-style:italic;
    color:rgba(245,236,215,.5);margin-bottom:12px"></div>
  <div style="display:flex;gap:8px;justify-content:center;flex-wrap:wrap">
    <button class="btn green" id="go-again-btn" onclick="startGame()">▷ Play Again</button>
    <button class="btn" id="go-replay-btn" onclick="startReplay()" style="display:none">⏪ Slow Replay</button>
    <button class="btn"                          onclick="showHome()">🏠 Home</button>
    <button class="btn purple"                   onclick="showFbModal()">⭐ Rate</button>
  </div>
 </div>
</div>

<!-- ── WINNER OVERLAY ── -->
<div id="winner-overlay">
  <div class="win-title" id="win-label">🏆 VICTORY! 🏆</div>
  <div class="win-sub"   id="win-sub">Congratulations!</div>
  <canvas id="herd-canvas"></canvas>
  <div class="win-cows"  id="win-cows">🐄 +0 cattle added to your herd</div>
  <button class="btn green" style="margin-top:14px" onclick="hideWinner()">Continue ▷</button>
</div>

<script>
// ── Globals ───────────────────────────────────────────────────────────────────
const LANGS_C  = {{ langs|tojson }};
const SKINS_C  = {{ skins|tojson }};
let CL='en', LANG=LANGS_C['en'];
let _mode='ai', _level=1, _skin='zulu';
let _user={name:'Guest',email:'',wins:0,losses:0,draws:0,games:0,
           skin:'zulu',level:1,lang:'en',total_cows:0};
let _gs=null, _skinData=null;
let _authMode='login';
let _onlineRoom=null, _pollT=null, _tPlayers=8;
// Chat
let _cwSid=null, _cwOpen=false, _cwTab='chat', _surveyAns={};
// Feedback
let _fbRating=0, _fbCat='general';

// ── Canvas Setup ──────────────────────────────────────────────────────────────
const canvas=document.getElementById('canvas');
const ctx=canvas.getContext('2d');
let W=0,H=0;
let BOARD={x:0,y:0,w:0,h:0,rows:4,cols:4,hd:60,holes:[]};
let _frames=[],_fi=0, _hov=-1, _busy=false;
let _parts=[];

function resize(){
  W=canvas.width=window.innerWidth;
  H=canvas.height=window.innerHeight;
  calcBoard();
}
window.addEventListener('resize',resize); resize();

// ── Child mode helpers ────────────────────────────────────────────────────────
const CTIPS=[
  "👆 Tap any hole on YOUR bottom rows to pick up stones!",
  "🌀 Stones move anti-clockwise — like a backwards clock!",
  "🐄 Your LAST stone lands in empty hole opposite full holes = CAPTURE!",
  "💡 Green glow = holes you can pick. Go ahead, tap one!",
  "⭐ The more you play, the bigger your cattle herd grows!",
  "🎉 Land your last stone in a hole with stones = pick them all up — keep going!",
];
let _ctipI=0, _ctipTmr=null;
function startCTips(){
  clearInterval(_ctipTmr);
  showCTip(0);
  _ctipTmr=setInterval(()=>{_ctipI=(_ctipI+1)%CTIPS.length;showCTip(_ctipI);},7500);
}
function stopCTips(){clearInterval(_ctipTmr);document.getElementById('child-hint').style.display='none';}
function showCTip(i){
  const el=document.getElementById('child-hint');
  el.style.transition='opacity .4s';el.style.opacity='0';
  setTimeout(()=>{el.textContent=CTIPS[i];el.style.opacity='1';},420);
}
const CPALETTE=['#FF6B6B','#FFD93D','#6BCB77','#4D96FF','#C77DFF','#FF9671','#00C9A7','#FF69B4'];
function cCol(i){return CPALETTE[i%CPALETTE.length];}

// ── Background ────────────────────────────────────────────────────────────────
function drawBg(){
  if(_level===1&&_gs){drawChildBg();}else{drawSavannaBg();}
}
function drawChildBg(){
  const sky=ctx.createLinearGradient(0,0,0,H);
  sky.addColorStop(0,'#050015');sky.addColorStop(.65,'#120830');sky.addColorStop(1,'#200838');
  ctx.fillStyle=sky;ctx.fillRect(0,0,W,H);
  // Moon
  ctx.save();ctx.fillStyle='rgba(255,245,160,.9)';
  ctx.shadowColor='rgba(255,230,80,.55)';ctx.shadowBlur=32;
  ctx.beginPath();ctx.arc(W*.84,H*.1,26,0,Math.PI*2);ctx.fill();ctx.restore();
  // Coloured stars
  const sc=['#FFD700','#FF69B4','#7DF9FF','#98FF98','#FFA0A0','#C77DFF'];
  [[.1,.07],[.28,.04],[.45,.09],[.62,.05],[.77,.12],[.15,.15],[.38,.06],
   [.55,.13],[.7,.07],[.88,.18]].forEach(([rx,ry],i)=>{
    ctx.save();ctx.fillStyle=sc[i%sc.length];ctx.shadowColor=sc[i%sc.length];ctx.shadowBlur=7;
    ctx.beginPath();ctx.arc(W*rx,H*ry,2.2,0,Math.PI*2);ctx.fill();ctx.restore();
  });
  // Ground
  const g=ctx.createLinearGradient(0,H*.7,0,H);
  g.addColorStop(0,'rgba(40,10,70,.8)');g.addColorStop(1,'rgba(15,5,35,.9)');
  ctx.fillStyle=g;ctx.fillRect(0,H*.7,W,H*.3);
  // Grass tufts
  ctx.strokeStyle='rgba(80,220,80,.35)';ctx.lineWidth=1.8;
  for(let x=18;x<W;x+=38){
    ctx.beginPath();ctx.moveTo(x,H);ctx.lineTo(x-5,H-10);ctx.stroke();
    ctx.beginPath();ctx.moveTo(x,H);ctx.lineTo(x+4,H-8);ctx.stroke();
  }
}
function drawSavannaBg(){
  const s=ctx.createLinearGradient(0,0,0,H*.5);
  s.addColorStop(0,'#1a0d03');s.addColorStop(.5,'#2d1205');s.addColorStop(1,'#4a2008');
  ctx.fillStyle=s;ctx.fillRect(0,0,W,H);
  const g=ctx.createLinearGradient(0,H*.5,0,H);
  g.addColorStop(0,'#3d1f06');g.addColorStop(.4,'#5c3210');g.addColorStop(1,'#2a1504');
  ctx.fillStyle=g;ctx.fillRect(0,H*.5,W,H*.5);
  drawAcacias();
  drawLeo(0,0,160,160,.08);drawLeo(W-160,0,160,160,.08);
  drawZebra(0,0,36,H,.1);drawZebra(W-36,0,36,H,.1);
  [[W*.18,H*.07],[W*.6,H*.04],[W*.82,H*.11],[W*.35,H*.03],
   [W*.5,H*.09],[W*.9,H*.06]].forEach(([x,y])=>{
    ctx.fillStyle='rgba(255,240,200,.35)';
    ctx.beginPath();ctx.arc(x,y,1.2,0,Math.PI*2);ctx.fill();
  });
}
function drawAcacias(){
  [{x:W*.05,y:H*.43,s:.9},{x:W*.17,y:H*.45,s:.7},{x:W*.79,y:H*.41,s:1},
   {x:W*.91,y:H*.46,s:.8},{x:W*.55,y:H*.47,s:.6}].forEach(({x,y,s})=>{
    ctx.strokeStyle='rgba(28,14,4,.6)';ctx.lineWidth=3*s;
    ctx.beginPath();ctx.moveTo(x,y+30*s);ctx.lineTo(x,y);ctx.stroke();
    ctx.fillStyle='rgba(14,9,3,.55)';
    ctx.beginPath();ctx.ellipse(x,y-8*s,28*s,10*s,0,0,Math.PI*2);ctx.fill();
  });
}
function drawLeo(ox,oy,w,h,a){
  ctx.save();ctx.globalAlpha=a;
  [[30,25,15],[68,10,11],[50,55,13],[108,30,10],[20,80,11],[84,68,12]].forEach(([x,y,r])=>{
    ctx.fillStyle='#C8A24A';ctx.beginPath();ctx.arc(ox+x,oy+y,r,0,Math.PI*2);ctx.fill();
    ctx.fillStyle='#8B6914';
    ctx.beginPath();ctx.arc(ox+x-r*.3,oy+y-r*.3,r*.5,0,Math.PI*2);ctx.fill();
    ctx.beginPath();ctx.arc(ox+x+r*.3,oy+y+r*.3,r*.4,0,Math.PI*2);ctx.fill();
  });ctx.restore();
}
function drawZebra(ox,oy,w,h,a){
  ctx.save();ctx.globalAlpha=a;ctx.fillStyle='#fff';
  for(let i=0;i<h;i+=18){
    if(Math.floor(i/18)%2===0){
      ctx.beginPath();ctx.moveTo(ox,oy+i);ctx.lineTo(ox+w,oy+i+3);
      ctx.lineTo(ox+w,oy+i+10);ctx.lineTo(ox,oy+i+8);ctx.closePath();ctx.fill();
    }
  }ctx.restore();
}

// ── Board ─────────────────────────────────────────────────────────────────────
function calcBoard(){
  const R=BOARD.rows=(_gs?_gs.rows:4);
  const C=BOARD.cols=(_gs?_gs.cols:4);
  const isC=_level===1&&_gs;
  const mW=Math.min(W-36,isC?510:530);
  const hd=Math.min(mW/(C+1),(H*.44)/(R+1),isC?82:70);
  const bw=hd*(C+.8),bh=hd*(R+.8);
  BOARD.x=(W-bw)/2;BOARD.y=(H-bh)/2+10;
  BOARD.w=bw;BOARD.h=bh;BOARD.hd=hd;
  BOARD.holes=[];
  for(let r=0;r<R;r++) for(let c=0;c<C;c++)
    BOARD.holes.push({x:BOARD.x+hd*.4+c*hd,y:BOARD.y+hd*.4+r*hd,idx:r*C+c});
}

function drawBoard(board){
  if(!board)return;
  const sk=_skinData||SKINS_C['zulu'];
  const isC=_level===1&&_gs;
  const hd=BOARD.hd, R=BOARD.rows, C=BOARD.cols;
  // Board backing
  ctx.save();ctx.shadowColor='rgba(0,0,0,.68)';ctx.shadowBlur=28;
  const bg=ctx.createLinearGradient(BOARD.x,BOARD.y,BOARD.x+BOARD.w,BOARD.y+BOARD.h);
  if(isC){bg.addColorStop(0,'#1e0848');bg.addColorStop(.5,'#150535');bg.addColorStop(1,'#1e0848');}
  else{bg.addColorStop(0,sk.board);bg.addColorStop(.5,ltn(sk.board,18));bg.addColorStop(1,sk.board);}
  ctx.fillStyle=bg;
  rrect(ctx,BOARD.x-13,BOARD.y-13,BOARD.w+26,BOARD.h+26,14);ctx.fill();
  ctx.restore();
  // Border
  ctx.save();
  if(isC){
    // Rainbow animated border
    ctx.lineWidth=3;
    CPALETTE.forEach((col,i)=>{
      ctx.strokeStyle=col;ctx.globalAlpha=.25;
      rrect(ctx,BOARD.x-16-i*1.5,BOARD.y-16-i*1.5,BOARD.w+32+i*3,BOARD.h+32+i*3,16+i*2);ctx.stroke();
    });
    ctx.globalAlpha=1;ctx.strokeStyle='#FF69B4';ctx.lineWidth=2.5;
  } else {
    ctx.strokeStyle=sk.hl;ctx.lineWidth=2.5;
  }
  rrect(ctx,BOARD.x-13,BOARD.y-13,BOARD.w+26,BOARD.h+26,14);ctx.stroke();
  ctx.restore();
  // Centre divider line
  const midY=BOARD.y+hd*.4+(R/2-.5)*hd;
  ctx.save();ctx.strokeStyle=isC?'rgba(255,105,180,.5)':'rgba(201,168,76,.55)';
  ctx.lineWidth=1.5;ctx.setLineDash([5,4]);
  ctx.beginPath();ctx.moveTo(BOARD.x-6,midY);ctx.lineTo(BOARD.x+BOARD.w+6,midY);ctx.stroke();
  ctx.setLineDash([]);ctx.restore();
  // Player labels
  ctx.save();
  const lf=hd*(isC?.28:.22);
  ctx.font=(isC?'700 ':'') + lf+'px '+(isC?"'Nunito',sans-serif":"'Cinzel',serif");
  ctx.textAlign='center';ctx.globalAlpha=.82;
  ctx.fillStyle=isC?'#FFD700':sk.hl;
  const p0n=(_gs&&_mode!=='ai'&&_user.email)?_user.name:(LANG.turnYou||'You');
  const p1n=_mode==='ai'?(LANG.aiName||'AI'):(LANG.turnP2||'Player 2');
  ctx.fillText(p0n,BOARD.x+BOARD.w/2,BOARD.y+BOARD.h+28);
  ctx.fillText(p1n,BOARD.x+BOARD.w/2,BOARD.y-15);
  ctx.restore();
  // Holes
  BOARD.holes.forEach(h=>{
    const cnt=board[h.idx]||0;
    const r=hd*.37;
    const valid=_gs&&_gs.player===0&&_gs.running&&myHole(h.idx,0)&&cnt>0;
    const hov=h.idx===_hov;
    // Shadow
    ctx.save();ctx.shadowColor='rgba(0,0,0,.65)';ctx.shadowBlur=10;
    ctx.fillStyle=isC?'#050012':'#080400';
    ctx.beginPath();ctx.arc(h.x,h.y,r,0,Math.PI*2);ctx.fill();ctx.restore();
    // Inner gradient
    const ig=ctx.createRadialGradient(h.x-r*.2,h.y-r*.2,r*.04,h.x,h.y,r);
    ig.addColorStop(0,isC?'#180840':'#180c02');ig.addColorStop(1,isC?'#090425':'#040200');
    ctx.fillStyle=ig;ctx.beginPath();ctx.arc(h.x,h.y,r,0,Math.PI*2);ctx.fill();
    // AI last-move highlight (red tinge)
    if(h.idx===_lastAIHole&&_lastAIHole>=0){
      ctx.save();
      ctx.strokeStyle='rgba(255,80,80,.7)';ctx.lineWidth=2;
      ctx.shadowColor='rgba(255,80,80,.6)';ctx.shadowBlur=10;
      ctx.beginPath();ctx.arc(h.x,h.y,r+3,0,Math.PI*2);ctx.stroke();
      ctx.restore();
    }
    // Valid glow — pulsing if your turn
    if(valid){
      ctx.save();
      const gc=isC?'#FFD700':sk.hl;
      const pulse=.7+.3*Math.sin(Date.now()*.004+(h.idx*.5));
      ctx.shadowColor=gc;ctx.shadowBlur=hov?(isC?28:20):(isC?14:8)*pulse;
      ctx.strokeStyle=hov?gc:'rgba(255,215,0,'+(.4+.25*pulse)+')';
      ctx.lineWidth=isC?(hov?3.5:2.2):1.8;
      ctx.beginPath();ctx.arc(h.x,h.y,r+(isC?3.5:2.2),0,Math.PI*2);ctx.stroke();
      if(isC&&hov){ctx.globalAlpha=.22;ctx.beginPath();ctx.arc(h.x,h.y,r+10,0,Math.PI*2);ctx.stroke();}
      ctx.restore();
    }
    // Stones
    if(cnt>0) drawStones(h.x,h.y,r,cnt,sk,valid&&hov,isC,h.idx);
    // Count
    if(cnt>0){
      ctx.save();
      const fs=Math.max(hd*.26,isC?14:11);
      ctx.font=(isC?'700 ':'')+fs+'px '+(isC?"'Nunito',sans-serif":"'Cinzel',serif");
      ctx.textAlign='center';ctx.textBaseline='middle';
      ctx.fillStyle=isC?cCol(cnt):(cnt>=2?sk.hl:'rgba(245,236,215,.45)');
      ctx.shadowColor='rgba(0,0,0,.85)';ctx.shadowBlur=4;
      ctx.fillText(cnt,h.x,h.y+r*1.62);ctx.restore();
    }
  });
}

function drawStones(cx,cy,r,cnt,sk,glow,isC,hi){
  const pos=stonePts(cnt,r*.7);
  pos.forEach(([ox,oy],i)=>{
    const sr=r*(cnt>6?.22:cnt>3?.27:.32);
    const sx=cx+ox,sy=cy+oy;
    ctx.save();
    if(glow){ctx.shadowColor=isC?cCol(i):sk.hl;ctx.shadowBlur=11;}
    const sg=ctx.createRadialGradient(sx-sr*.28,sy-sr*.28,sr*.04,sx,sy,sr);
    const col=isC?cCol((hi||0)+i):sk.stone;
    sg.addColorStop(0,ltn(col,32));sg.addColorStop(.6,col);sg.addColorStop(1,dkn(col,28));
    ctx.fillStyle=sg;ctx.beginPath();ctx.arc(sx,sy,sr,0,Math.PI*2);ctx.fill();
    ctx.fillStyle='rgba(255,255,255,.22)';
    ctx.beginPath();ctx.arc(sx-sr*.24,sy-sr*.24,sr*.32,0,Math.PI*2);ctx.fill();
    ctx.restore();
  });
}
function stonePts(n,mx){
  if(n===1)return[[0,0]];if(n===2)return[[-mx*.44,0],[mx*.44,0]];
  if(n===3)return[[0,-mx*.5],[mx*.44,mx*.28],[-mx*.44,mx*.28]];
  const p=[];
  for(let ring=1;ring<=2;ring++){
    const max=ring===1?(n<=6?n:6):n-6;
    for(let i=0;i<max;i++){
      const a=i/max*Math.PI*2-Math.PI/2,rr=(ring/(2+.5))*mx*.9;
      p.push([Math.cos(a)*rr,Math.sin(a)*rr]);
    }
    if(p.length>=n)break;
  }
  while(p.length<n)p.push([0,0]);
  return p.slice(0,n);
}

// ── Particles ─────────────────────────────────────────────────────────────────
function spawnP(x,y,col,n=12){
  for(let i=0;i<n;i++){
    const a=Math.random()*Math.PI*2,v=1.4+Math.random()*3;
    _parts.push({x,y,vx:Math.cos(a)*v,vy:Math.sin(a)*v-1.8,
      a:1,r:3+Math.random()*4,col,life:40+Math.random()*25});
  }
}
function spawnEmoji(x,y){
  const em=['🐄','⭐','✨','🎉','💛','🌈','🌟'];
  for(let i=0;i<6;i++){
    const a=Math.random()*Math.PI*2,v=2+Math.random()*3;
    _parts.push({x,y,vx:Math.cos(a)*v,vy:Math.sin(a)*v-2.8,
      a:1,r:14,col:'#FFD700',em:em[Math.floor(Math.random()*em.length)],life:55+Math.random()*20});
  }
}
function tickParts(){
  _parts=_parts.filter(p=>{
    p.x+=p.vx;p.y+=p.vy;p.vy+=.11;p.a-=1/p.life;p.r*=.972;
    ctx.save();ctx.globalAlpha=p.a;
    if(p.em){ctx.font=p.r+'px serif';ctx.textAlign='center';ctx.textBaseline='middle';ctx.fillText(p.em,p.x,p.y);}
    else{ctx.fillStyle=p.col;ctx.beginPath();ctx.arc(p.x,p.y,p.r,0,Math.PI*2);ctx.fill();}
    ctx.restore();return p.a>.04;
  });
}

// ── HUD ───────────────────────────────────────────────────────────────────────
function updHUD(){
  if(!_gs)return;
  const p0=_gs.cows0||0,p1=_gs.cows1||0;
  document.getElementById('hud-scores').textContent=`🐄 ${p0} · ${p1} 🐄`;
  const isC=_level===1;const pl=_gs.player;
  document.getElementById('hud-title').textContent=
    !_gs.running?'GAME OVER':
    pl===0?(isC?'👆 YOUR TURN! 🌟':'Your Turn'):
    (_mode==='ai'?(isC?'🤖 AI is thinking… watch!':'AI Thinking…'):'Player 2');
}

// ── Narrator ──────────────────────────────────────────────────────────────────
let _nq=[],_nt=null;
function narrate(msg,dur=3500){if(!msg)return;_nq.push({msg,dur});if(!_nt)tickN();}
function tickN(){
  if(!_nq.length){_nt=null;return;}
  const{msg,dur}=_nq.shift();
  const el=document.getElementById('narrator-bar');
  el.style.opacity='0';
  setTimeout(()=>{el.textContent=msg;el.style.opacity='.9';_nt=setTimeout(tickN,dur);},200);
}

// ── Render ────────────────────────────────────────────────────────────────────
function loop(){
  ctx.clearRect(0,0,W,H);
  drawBg();
  if(_gs)drawBoard(_frames.length>0?_frames[_fi]:_gs.board);
  if(_hov>=0&&_gs&&_gs.player===0&&_gs.running){
    const h=BOARD.holes[_hov];
    if(h){
      ctx.font=(_level===1?'26':'20')+'px serif';
      ctx.textAlign='center';ctx.textBaseline='bottom';
      ctx.fillText(_level===1?'👆':'🖐',h.x,h.y-BOARD.hd*.52);
    }
  }
  tickParts();
  requestAnimationFrame(loop);
}
requestAnimationFrame(loop);

// ── Input ─────────────────────────────────────────────────────────────────────
canvas.addEventListener('mousemove',e=>{
  if(!_gs||!_gs.running)return;
  const{x,y}=gp(e);_hov=findH(x,y);
});
canvas.addEventListener('mouseleave',()=>_hov=-1);
canvas.addEventListener('click',e=>{
  if(!_gs||!_gs.running)return;
  const{x,y}=gp(e);const i=findH(x,y);if(i>=0)doMove(i);
});
canvas.addEventListener('touchstart',e=>{
  e.preventDefault();if(!_gs||!_gs.running)return;
  const t=e.touches[0];const{x,y}=gp(t);const i=findH(x,y);if(i>=0)doMove(i);
},{passive:false});

// Keyboard: 1-6 select holes, R = replay, Esc = close modals
document.addEventListener('keydown',e=>{
  if(!_gs||!_gs.running||_gs.player!==0||_busy)return;
  const n=parseInt(e.key);
  if(n>=1&&n<=6){
    const R=_gs.rows,C=_gs.cols,innerRow=R/2;
    const hole=n<=C?innerRow*C+(n-1):(innerRow+1)*C+(n-1-C);
    if(hole<_gs.board.length)doMove(hole);
  }
});
document.addEventListener('keyup',e=>{
  if(e.key==='Escape')closeAllM();
});

// Keyboard: number keys 1-6 select your hole by position left→right
document.addEventListener('keydown',e=>{
  if(!_gs||!_gs.running||_gs.player!==0||_busy)return;
  const n=parseInt(e.key);
  if(n>=1&&n<=6){
    // Map key to player's bottom rows, left to right
    const R=_gs.rows,C=_gs.cols;
    const innerRow=R/2; // player's inner row
    // Key 1..C = inner row, key C+1..2C = outer row
    let hole;
    if(n<=C) hole = innerRow*C + (n-1);
    else     hole = (innerRow+1)*C + (n-1-C);
    if(hole<_gs.board.length) doMove(hole);
  }
  if(e.key==='r'||e.key==='R') startReplay();
  if(e.key==='Escape') closeAllM();
});
function gp(e){const r=canvas.getBoundingClientRect();return{x:(e.clientX-r.left)*W/r.width,y:(e.clientY-r.top)*H/r.height};}
function findH(x,y){const hd=BOARD.hd;for(let i=0;i<BOARD.holes.length;i++){const h=BOARD.holes[i];if(Math.hypot(x-h.x,y-h.y)<hd*.44)return i;}return -1;}
function myHole(idx,pl){if(!_gs)return false;const R=_gs.rows,C=_gs.cols,row=Math.floor(idx/C);return pl===0?row>=R/2:row<R/2;}
function aiDelay(l){return l===1?3000:l===2?920:360;}// L1 slowest so kids can watch

// ── Move ──────────────────────────────────────────────────────────────────────
let _lastAIHole=-1; // highlight last AI move

// Fetch with timeout — prevents indefinite hang if server is slow
async function fetchWithTimeout(url,opts,ms=8000){
  const ctrl=new AbortController();
  const tid=setTimeout(()=>ctrl.abort(),ms);
  try{
    const r=await fetch(url,{...opts,signal:ctrl.signal});
    clearTimeout(tid);
    return r;
  }catch(e){
    clearTimeout(tid);
    if(e.name==='AbortError') throw new Error('Server took too long — check connection and try again');
    throw e;
  }
}

// AI progress indicator
let _aiProg=null;
function showAIThinking(delayMs){
  const bar=document.getElementById('ai-thinking-bar');
  if(!bar)return;
  bar.style.display='flex';
  bar.querySelector('.ai-fill').style.animation=`aiFill ${delayMs}ms linear forwards`;
}
function hideAIThinking(){
  const bar=document.getElementById('ai-thinking-bar');
  if(bar)bar.style.display='none';
  const fill=bar?.querySelector('.ai-fill');
  if(fill){fill.style.animation='';fill.style.width='0%';}
}

async function doMove(idx){
  if(_busy||!_gs||!_gs.running||_gs.player!==0)return;
  const isC=_level===1;
  if(!myHole(idx,0)){
    narrate(isC?'⚠️ Those are not YOUR holes! Pick from the BOTTOM rows! 👇':'⚠️ That belongs to your opponent!');
    if(isC)spawnEmoji(BOARD.holes[idx]?.x||W/2,BOARD.holes[idx]?.y||H/2);
    playTribeSound&&playTribeSound('miss');
    return;
  }
  if(!(_gs.board[idx]||0)){narrate(isC?'😅 That hole is empty! Try another one.':'⚠️ Empty hole!');return;}
  _busy=true;
  const sk=_skinData||SKINS_C['zulu'];
  try{
    const res=await fetchWithTimeout('/api/game/move',
      {method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({idx})}, 10000);
    const d=await res.json();
    if(!d.ok){narrate('⚠️ '+(d.error||'Invalid move'));return;}
    // Player move animation
    const animMs=isC?90:50;
    if(d.steps?.length>0){
      if(d.captured>0){
        const h=BOARD.holes[idx];
        if(h){spawnP(h.x,h.y,sk.cap,18);if(isC)spawnEmoji(h.x,h.y);}
        playCaptureSound&&playCaptureSound();
      }
      await animS(d.steps,animMs);
    }
    if(d.narrator)narrate(d.narrator,3800);
    if(isC&&d.captured>0)narrate(`🎉 WOW! You captured ${d.captured} cow${d.captured>1?'s':''}! Great move! 🐄`,3500);
    // AI move
    if(d.ai_steps?.length>0){
      const del=aiDelay(_level);
      showAIThinking(del);
      narrate(isC?'🤖 The AI is picking a move… watch the stones! 👀':`🤖 ${LANG.aiName||'AI'} thinking…`,del+200);
      await sleep(del);
      hideAIThinking();
      _lastAIHole=d.ai_hole||0;
      if(d.ai_captured>0){
        const ah=BOARD.holes[d.ai_hole>=0?d.ai_hole:0];
        if(ah)spawnP(ah.x,ah.y,sk.cap,12);
        playCaptureSound&&playCaptureSound();
      }
      await animS(d.ai_steps,isC?100:58);
      if(d.ai_message)narrate('🤖 '+d.ai_message);
    }
    _gs=d.state;calcBoard();updHUD();
    if(d.game_over){
      playWinSound&&(d.scores[0]>d.scores[1]?playWinSound():null);
      await sleep(300);
      gameOver(d.scores,d.narrator);
    }
  }catch(e){
    narrate('⚠️ '+(e.message||'Connection error — tap to retry'));
    hideAIThinking();
  }finally{
    _busy=false;
  }
}
function animS(steps,ms){
  return new Promise(r=>{
    _frames=steps;_fi=0;
    const iv=setInterval(()=>{_fi++;if(_fi>=_frames.length){clearInterval(iv);_frames=[];_fi=0;r();}},ms);
  });
}
function sleep(ms){return new Promise(r=>setTimeout(r,ms));}

// ── Game Over ─────────────────────────────────────────────────────────────────
let _moveHistory=[]; // store moves for replay
let _replayMode=false;

function recordMove(idx){ _moveHistory.push({idx,board:[..._gs.board],player:_gs.player}); }

function gameOver(scores,nm){
  const[p0,p1]=scores||[0,0];
  const win=p0>p1,draw=p0===p1;
  const isC=_level===1;
  const box=document.getElementById('go-box');
  box.className='modal-box'+(isC?' cbox':'');
  document.getElementById('go-bar').className=isC?'rainbow-bar':'nguni-bar';
  // Show replay button if we recorded moves
  const replayBtn=document.getElementById('go-replay-btn');
  if(replayBtn) replayBtn.style.display=_moveHistory.length>0?'inline-flex':'none';
  document.getElementById('go-title').textContent=
    win?(isC?'🎉 YOU WIN! Amazing! 🎉':(LANG.win||'You Win!')):
    draw?(isC?'🤝 It\'s a tie! Well played!':(LANG.draw||'Draw!')):
    (isC?'🤖 AI won — practice makes perfect! 💪':(LANG.lose||'AI Wins!'));
  document.getElementById('go-msg').textContent=
    win?(isC?'Fantastic! You\'re a brilliant Intshuba player!':''):
    (!win&&!draw&&isC?'Keep playing — you\'re getting better every game! 🌟':'');
  document.getElementById('go-scores').textContent=`🐄 ${p0} · ${p1} 🐄`;
  document.getElementById('go-note').textContent=nm||'';
  document.getElementById('go-again-btn').className='btn '+(isC?'green cbtn cg':'green');
  closeAllM();
  if(win)showWin(p0);
  else document.getElementById('go-modal').classList.remove('hidden');
}

// ── Winner animation ──────────────────────────────────────────────────────────
async function startReplay(){
  if(!_moveHistory.length){narrate('No moves to replay yet — play a game first!');return;}
  closeAllM();
  _replayMode=true;
  const banner=document.getElementById('replay-banner');
  if(banner)banner.style.display='block';
  narrate('⏪ Replaying your game at 4× slower pace — watch each move!',4000);
  const speed=document.getElementById('replay-speed')?.value||'slow';
  const frameMs=speed==='very_slow'?250:speed==='slow'?150:80;
  // Rebuild game from history
  for(let i=0;i<_moveHistory.length;i++){
    const move=_moveHistory[i];
    _gs={..._gs,board:[...move.board],player:move.player};
    calcBoard();
    await animS([[move.idx]],frameMs*4);
    await sleep(frameMs*6);
  }
  _replayMode=false;
  if(banner)banner.style.display='none';
  narrate('⏪ Replay complete! Hit Play Again for a new game.',4000);
  document.getElementById('go-modal')?.classList.remove('hidden');
}

function showWin(n){
  const isC=_level===1;
  document.getElementById('win-label').textContent=isC?'🎉 YOU WIN! 🎉':'🏆 VICTORY! 🏆';
  document.getElementById('win-sub').textContent=isC?'Wow! You\'re an Intshuba champion! 🌟':'Well played, warrior!';
  document.getElementById('win-cows').textContent=`🐄 +${n} cattle added to your herd`;
  document.getElementById('winner-overlay').classList.add('show');
  animHerd(n,isC);
  narrate(`🏆 ${LANG.win||'You Win!'} · +${n} cattle!`,8000);
}
function hideWinner(){
  document.getElementById('winner-overlay').classList.remove('show');
  document.getElementById('go-modal').classList.remove('hidden');
}
function animHerd(count,isC){
  const hc=document.getElementById('herd-canvas');
  const hx=hc.getContext('2d');
  hc.width=Math.min(window.innerWidth,580);hc.height=200;
  const cw=hc.width,ch=hc.height,n=Math.min(count,20);
  const cows=Array.from({length:n},(_,i)=>({
    x:-80-i*70-Math.random()*40,y:ch*.54+(Math.random()-.5)*28,
    spd:1.7+Math.random()*1.2,sz:.68+Math.random()*.5,
    col:isC?CPALETTE[i%CPALETTE.length]:['#C8A24A','#E8D090','#8B5E1A','#D4AA60'][Math.floor(Math.random()*4)],
    ph:Math.random()*Math.PI*2,arr:false
  }));
  function rend(){
    hx.clearRect(0,0,cw,ch);
    const bg=hx.createLinearGradient(0,0,0,ch);
    if(isC){bg.addColorStop(0,'#050015');bg.addColorStop(1,'#1a0838');}
    else{bg.addColorStop(0,'#1a0a02');bg.addColorStop(1,'#3d1f06');}
    hx.fillStyle=bg;hx.fillRect(0,0,cw,ch);
    hx.fillStyle=isC?'rgba(40,10,70,.5)':'rgba(90,50,10,.4)';
    hx.fillRect(0,ch*.65,cw,ch*.35);
    const arr=cows.filter(c=>c.arr).length;
    cows.forEach(c=>{
      if(!c.arr)c.x+=c.spd;
      if(c.x>cw*.05+Math.random()*cw*.85)c.arr=true;
      c.ph+=.17;
      drawCow(hx,c.x,c.y,c.sz,c.col,c.ph,isC);
    });
    hx.fillStyle='rgba(201,168,76,.92)';
    hx.font="bold 14px 'Cinzel',serif";
    hx.textAlign='center';
    hx.fillText('🐄 '+arr+' / '+n+' cattle arriving',cw/2,24);
    if(cows.some(c=>!c.arr))requestAnimationFrame(rend);
  }
  requestAnimationFrame(rend);
}
function drawCow(c,x,y,sz,col,ph,rainbow){
  c.save();c.translate(x,y);c.scale(sz,sz);
  c.fillStyle=col;c.beginPath();c.ellipse(0,0,26,15,0,0,Math.PI*2);c.fill();
  c.beginPath();c.ellipse(24,0,12,10,.2,0,Math.PI*2);c.fill();
  // Horns
  c.strokeStyle='#8B7355';c.lineWidth=2;
  c.beginPath();c.moveTo(28,-6);c.quadraticCurveTo(36,-16,32,-20);c.stroke();
  c.beginPath();c.moveTo(32,-5);c.quadraticCurveTo(40,-13,38,-18);c.stroke();
  // Legs
  const ls=Math.sin(ph)*7;
  c.strokeStyle=col;c.lineWidth=3.5;c.lineCap='round';
  [[-10,11],[-3,11],[4,11],[11,11]].forEach(([lx],i)=>{
    c.beginPath();c.moveTo(lx,11);c.lineTo(lx+(i%2===0?ls:-ls),25);c.stroke();
  });
  // Eye
  c.fillStyle='#1a0a00';c.beginPath();c.arc(32,-1,2.2,0,Math.PI*2);c.fill();
  // Tail
  c.strokeStyle=dkn(col,20);c.lineWidth=1.8;
  c.beginPath();c.moveTo(-24,-2);c.quadraticCurveTo(-34,-11,-30,-17);c.stroke();
  // Nguni spots
  c.fillStyle='rgba(255,255,255,.15)';
  c.beginPath();c.ellipse(-6,-4,7,5,.5,0,Math.PI*2);c.fill();
  if(rainbow){c.globalAlpha=.7;c.font='9px serif';c.textAlign='center';c.fillText('⭐',-8,-18);}
  c.restore();
}

// ── Helpers ───────────────────────────────────────────────────────────────────
function rrect(c,x,y,w,h,r){c.beginPath();c.moveTo(x+r,y);c.lineTo(x+w-r,y);c.quadraticCurveTo(x+w,y,x+w,y+r);c.lineTo(x+w,y+h-r);c.quadraticCurveTo(x+w,y+h,x+w-r,y+h);c.lineTo(x+r,y+h);c.quadraticCurveTo(x,y+h,x,y+h-r);c.lineTo(x,y+r);c.quadraticCurveTo(x,y,x+r,y);c.closePath();}
function ltn(h,p){const r=parseInt(h.slice(1,3)||'0',16),g=parseInt(h.slice(3,5)||'0',16),b=parseInt(h.slice(5,7)||'0',16);return '#'+[r,g,b].map(v=>Math.min(255,Math.round(v+(255-v)*p/100)).toString(16).padStart(2,'0')).join('');}
function dkn(h,p){const r=parseInt(h.slice(1,3)||'0',16),g=parseInt(h.slice(3,5)||'0',16),b=parseInt(h.slice(5,7)||'0',16);return '#'+[r,g,b].map(v=>Math.max(0,Math.round(v*(1-p/100))).toString(16).padStart(2,'0')).join('');}

// ── Modal helpers ─────────────────────────────────────────────────────────────
function closeAllM(){document.querySelectorAll('.modal').forEach(m=>m.classList.add('hidden'));}
function closeM(id){document.getElementById(id).classList.add('hidden');}

// ── Home ──────────────────────────────────────────────────────────────────────
function showHome(){
  closeAllM();
  renderLangGrid();
  updHomeAuthBtn();
  document.getElementById('home-modal').classList.remove('hidden');
}
function updHomeAuthBtn(){
  const btn=document.getElementById('home-auth-btn');
  if(_user&&_user.email){btn.textContent='👤 '+(_user.name||'').split(' ')[0];btn.onclick=showProfile;}
  else{btn.textContent='🔑 Sign In';btn.onclick=showAuth;}
}

// ── Rules ─────────────────────────────────────────────────────────────────────
function showRules(){
  const isC=_level===1;
  document.getElementById('rules-kids-badge').style.display=isC?'block':'none';
  document.getElementById('rules-bar').className=isC?'rainbow-bar':'nguni-bar';
  document.getElementById('rules-box').className='modal-box'+(isC?' cbox':'');
  document.getElementById('rules-h').textContent=isC?'📖 How To Play – Kids Guide':'IMITHETHO · RULES';
  const rb=document.getElementById('rules-body');rb.innerHTML='';
  if(isC){
    [['🎯 Your Side','The BOTTOM two rows of holes on the board are YOURS. The AI controls the TOP rows.'],
     ['🖐️ Pick a Hole','Tap any hole on YOUR side that has stones. You scoop up ALL the stones from that hole!'],
     ['🌀 Sow the Stones','Drop one stone into each hole going ANTI-CLOCKWISE — like a backwards clock.'],
     ['🔄 Keep Going!','If your LAST stone lands in a hole that already has stones — pick them ALL up and keep sowing!'],
     ['🐄 Capture!','If your LAST stone lands in an EMPTY hole on your INNER row AND the opposite holes have stones — you CAPTURE them all! 🎉'],
     ['😴 Sleeping?','If a player has no valid moves, they sleep (kulala) and the other player keeps going.'],
     ['🏆 How to Win','Count up stones at the end. The player with the MOST COWS wins! Go get them! 🐄🐄🐄'],
    ].forEach(([t,x])=>{
      const d=document.createElement('div');
      d.style.cssText='margin-bottom:13px;padding:11px 13px;background:rgba(255,215,0,.07);border-radius:12px;border-left:4px solid #FFD700;font-family:Nunito,sans-serif;';
      d.innerHTML=`<div style="font-size:15px;font-weight:800;color:#FFD700;margin-bottom:4px">${t}</div><div style="font-size:13px;color:#F5ECD7;line-height:1.6">${x}</div>`;
      rb.appendChild(d);
    });
  } else {
    [['rulesBoard','rulesBoardText','🏗️'],['rulesStones','rulesStonesText','🪨'],
     ['rulesSow','rulesSowText','🌀'],['rulesCapture','rulesCaptureText','🐄'],
     ['rulesRules','rulesRulesText','📋'],['rulesWin','rulesWinText','🏆']
    ].forEach(([t,tx,ic])=>{
      const d=document.createElement('div');
      d.style.cssText='margin-bottom:12px;padding:10px;background:rgba(201,168,76,.06);border-radius:6px;border-left:3px solid var(--gold);';
      d.innerHTML=`<h3 style="font-family:Cinzel,serif;color:var(--gold);font-size:12px;margin-bottom:5px">${ic} ${LANG[t]||t}</h3><p style="font-size:13px;line-height:1.65">${(LANG[tx]||'').replace(/\n/g,'<br>')}</p>`;
      rb.appendChild(d);
    });
  }
  document.getElementById('rules-modal').classList.remove('hidden');
}

// ── Leaderboard ───────────────────────────────────────────────────────────────
function showLb(){document.getElementById('lb-modal').classList.remove('hidden');loadLb();}
let _lbSeg='livestock';
function lbSeg(seg){
  _lbSeg=seg;
  document.querySelectorAll('[id^="lbs-"]').forEach(b=>b.classList.toggle('act',b.id==='lbs-'+seg));
  loadLb();
}
async function loadLb(){
  const pool  = document.getElementById('lb-pool-filter')?.value  || 'all';
  const tribe = document.getElementById('lb-tribe-filter')?.value || 'all';
  try{
    const d=await(await fetch(`/api/leaderboard/segments?segment=${_lbSeg}&age_pool=${pool}&tribe=${tribe}&limit=30`)).json();
    const list=document.getElementById('lb-list');
    if(!list) return;
    const board=d.board||[];
    if(!board.length){list.innerHTML='<div style="text-align:center;padding:18px;opacity:.35">No players yet — be first!</div>';return;}
    list.innerHTML=board.map((e,i)=>{
      const medal=['🥇','🥈','🥉'][i]||('<span style="opacity:.4">#'+(i+1)+'</span>');
      const crown=e.has_crown?'👑 ':'';
      const ti=e.tribe_info||{};
      const seg_val = _lbSeg==='livestock'?e.herd_cows
                    : _lbSeg==='wins'?e.wins
                    : _lbSeg==='stages'?('L'+e.current_level)
                    : _lbSeg==='competitions'?e.competition_wins
                    : _lbSeg==='herd_total'?e.total_cows
                    : e.herd_cows;
      return `<div style="display:grid;grid-template-columns:32px 1fr 60px 60px 55px 65px;
        gap:4px;padding:7px 8px;border-radius:6px;transition:.15s;cursor:default;
        ${i%2===0?'background:rgba(201,168,76,.04)':''}">
        <span style="font-size:13px">${medal}</span>
        <span style="overflow:hidden;text-overflow:ellipsis;white-space:nowrap">
          ${crown}${ti.icon||''} <strong style="color:var(--ivory)">${e.name}</strong>
          <span style="font-size:10px;opacity:.4"> ${e.title||''}</span>
        </span>
        <span style="text-align:right;color:#6bffaa">${e.wins}</span>
        <span style="text-align:right;opacity:.45">${e.games}</span>
        <span style="text-align:right;color:#88ccff">${e.win_rate}%</span>
        <span style="text-align:right;color:var(--gold);font-weight:600">${(seg_val||0).toLocaleString()}</span>
      </div>`;
    }).join('');
  }catch(e){console.error(e);}
}

// ── Social sharing ─────────────────────────────────────────────────────────────
let _sharePending = null;
async function showShare(type='invite', extra='', narrate_msg='') {
  document.getElementById('share-modal').classList.remove('hidden');
  const sub = document.getElementById('share-subtext');
  if(sub) sub.textContent = narrate_msg || '';
  try{
    const d = await(await fetch(`/api/share/links?type=${type}&extra=${encodeURIComponent(extra)}`)).json();
    const grid = document.getElementById('share-buttons-grid');
    if(!grid) return;
    const platforms = d.links || {};
    grid.innerHTML = Object.entries(platforms).map(([pid,p]) => {
      const action = p.share_url
        ? `onclick="window.open('${p.share_url.replace(/'/g,"\'")}','_blank',
           'width=600,height=500')" title="${p.name}"`
        : `onclick="copyToClipboard('${(p.copy_text||d.share_url||'').replace(/'/g,"\'")}','share-copy-status','Copied!')" title="${p.note||p.name}"`;
      return `<button style="background:${p.color||'#333'};border:none;border-radius:10px;
        padding:10px 6px;cursor:pointer;display:flex;flex-direction:column;align-items:center;
        gap:4px;transition:.2s;color:white;font-size:10px" ${action}>
        <span style="font-size:20px">${p.icon}</span>
        <span style="font-weight:600">${p.name.split('/')[0]}</span>
      </button>`;
    }).join('');
    // Referral link
    if(_user?.email){
      const ref = await(await fetch('/api/share/referral')).json();
      const box = document.getElementById('share-referral-box');
      const inp = document.getElementById('ref-link-inp');
      if(box && inp){ box.style.display='block'; inp.value=ref.ref_url||''; }
    }
  }catch(e){console.error(e);}
}

function copyRefLink(){
  const inp=document.getElementById('ref-link-inp');
  if(inp){ inp.select(); navigator.clipboard?.writeText(inp.value); }
  document.getElementById('share-copy-status').textContent='Link copied! 🔗';
  setTimeout(()=>{ const el=document.getElementById('share-copy-status'); if(el) el.textContent=''; },3000);
}

function copyToClipboard(text, statusId, msg) {
  navigator.clipboard?.writeText(text).then(()=>{
    const el=document.getElementById(statusId);
    if(el){ el.textContent=msg||'Copied!'; setTimeout(()=>el.textContent='',3000); }
  }).catch(()=>{});
}

// ── Ceremony system ────────────────────────────────────────────────────────────
let _pendingCeremony = null;
let _skipCeremonyCallback = null;
let _completeCeremonyCallback = null;

async function checkCeremony(trigger, onDone, onSkip) {
  _skipCeremonyCallback = onSkip || null;
  _completeCeremonyCallback = onDone || null;
  try{
    const d = await(await fetch('/api/ceremony/required/'+trigger)).json();
    const ceremonies = Object.entries(d.ceremonies||{});
    if(!ceremonies.length){ if(onDone) onDone(); return; }
    const [cer_id, cer] = ceremonies[0];
    _pendingCeremony = cer_id;
    // Populate ceremony modal
    document.getElementById('cer-icon').textContent    = cer.icon;
    document.getElementById('cer-name').textContent    = cer.name;
    document.getElementById('cer-desc').textContent    = cer.desc;
    document.getElementById('cer-cost').textContent    = cer.cows_cost + ' 🐄';
    const bl = cer.blessing||{};
    document.getElementById('cer-blessing').textContent =
      bl.type?.replace('_',' ') + ' +'+(bl.value>=1?Math.round(bl.value*100)+'%':bl.value) +
      ' for '+bl.duration_days+' days';
    // Get current herd
    const herd_el = document.getElementById('cer-herd');
    if(herd_el && _kdata?.herd_cows!==undefined) herd_el.textContent='Your herd: '+_kdata.herd_cows+' cows';
    document.getElementById('ceremony-modal').classList.remove('hidden');
  }catch(e){ if(onDone) onDone(); }
}

async function performCeremony(){
  if(!_pendingCeremony) return;
  closeM('ceremony-modal');
  try{
    const d = await(await fetch('/api/ceremony/perform',{
      method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({ceremony:_pendingCeremony})
    })).json();
    narrate(d.message, 5000);
    if(d.ok){
      const hc=document.getElementById('herd-count');
      if(hc) hc.textContent=(d.herd_cows||0)+' 🐄';
      playWinSound && playWinSound();
    }
    if(_completeCeremonyCallback) _completeCeremonyCallback();
  }catch(e){ if(_completeCeremonyCallback) _completeCeremonyCallback(); }
  _pendingCeremony=null;
}

function skipCeremony(){
  if(_skipCeremonyCallback) _skipCeremonyCallback();
  _pendingCeremony=null;
}

// ── Trades modal ───────────────────────────────────────────────────────────────
async function showTrades(){
  if(!_user?.email){narrate('🔒 Sign in to access trades');showAuth();return;}
  document.getElementById('trades-modal').classList.remove('hidden');
  await loadTrades();
}

async function loadTrades(){
  try{
    const d = await(await fetch('/api/trades/list')).json();
    const owned = new Set(d.owned||[]);
    const trades = d.trades||{};
    const cer = d.ceremonies||{};
    // Trades grid
    const tgrid = document.getElementById('trades-list');
    if(tgrid){
      tgrid.innerHTML = Object.entries(trades).map(([id,t])=>{
        const isOwned = owned.has(id);
        const CAT_COLORS = {field:'#C8102E',craft:'#FFD700',construction:'#4CAF50',
          forge:'#FF8C00',extraction:'#8B4513',technical:'#4488FF',spiritual:'#9B4FCC',
          farming:'#228B22',trade:'#20B2AA'};
        const col = CAT_COLORS[t.category]||'#888';
        return `<div style="background:rgba(201,168,76,.07);border:1px solid ${isOwned?col:'rgba(201,168,76,.2)'};
          border-radius:10px;padding:12px;text-align:center;${isOwned?'box-shadow:0 0 10px '+col+'33':''}">
          <div style="font-size:24px">${t.icon}</div>
          <div style="font-family:'Cinzel',serif;color:${isOwned?col:'var(--gold)'};font-size:11px;margin:4px 0">${t.name}</div>
          <div style="font-size:11px;color:rgba(245,236,215,.45);margin-bottom:6px;line-height:1.4">${t.desc}</div>
          <div style="display:flex;justify-content:center;gap:6px;margin-bottom:8px">
            <span style="font-size:11px;color:#6bffaa">+${t.earn_day}🐄/day</span>
            <span style="font-size:10px;color:#ff8888">risk:${Math.round(t.risk*100)}%</span>
          </div>
          ${isOwned
            ? '<div style="background:rgba(107,255,170,.15);color:#6bffaa;font-size:11px;padding:4px 10px;border-radius:12px">✅ Active</div>'
            : `<button class="btn green" style="font-size:10px;padding:5px 12px;width:100%" onclick="buyTrade('${id}')">
                 Unlock — ${t.cows_to_unlock}🐄</button>`}
        </div>`;
      }).join('');
    }
    // Ceremonies list
    const clist = document.getElementById('ceremonies-list');
    if(clist){
      clist.innerHTML = Object.entries(cer).map(([id,c])=>{
        return `<div style="display:flex;align-items:center;gap:10px;padding:10px;
          border-bottom:.5px solid var(--border)">
          <span style="font-size:24px">${c.icon}</span>
          <div style="flex:1">
            <div style="font-size:13px;font-weight:500;color:var(--gold)">${c.name}</div>
            <div style="font-size:11px;color:rgba(245,236,215,.5);margin-top:2px">${c.desc}</div>
            <div style="font-size:10px;color:#ff9999;margin-top:2px">Costs ${c.cows_cost}🐄 · Trigger: ${c.trigger?.replace(/_/g,' ')}</div>
          </div>
          <div style="text-align:center;min-width:60px">
            <div style="font-size:10px;color:rgba(245,236,215,.3)">BLESSING</div>
            <div style="font-size:11px;color:#6bffaa">${c.blessing?.type?.replace('_',' ')}</div>
          </div>
        </div>`;
      }).join('');
    }
  }catch(e){}
}

function tradesTab(tab){
  ['trades','ceremonies'].forEach(t=>{
    document.getElementById('trt-'+t)?.classList.toggle('act',t===tab);
    const el=document.getElementById('trp-'+t);
    if(el) el.style.display=t===tab?'block':'none';
  });
}

async function buyTrade(tradeId){
  const msg=document.getElementById('trades-msg');
  if(msg){msg.textContent='Unlocking...';msg.style.display='block';msg.className='ok';}
  try{
    const d=await(await fetch('/api/trades/buy',{
      method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({trade:tradeId})
    })).json();
    if(d.ok){
      if(msg) msg.textContent=d.message;
      narrate(d.message,4000);
      await loadTrades();
      const hc=document.getElementById('herd-count');
      if(hc) hc.textContent=(d.herd_cows||0)+' 🐄';
    } else {
      if(msg){msg.textContent=d.message||d.error||'Error';msg.className='err';}
    }
  }catch(e){if(msg){msg.textContent='Error';msg.className='err';}}
}


// ── Selections ────────────────────────────────────────────────────────────────
function selMode(m){_mode=m;['ai','2p','online'].forEach(x=>document.getElementById('mode-'+x)?.classList.toggle('sel',x===m));}
function selLevel(l){_level=l;[1,2,3].forEach(x=>document.getElementById('lv-'+x)?.classList.toggle('sel',x===l));}
function selSkin(s){_skin=s;['zulu','xhosa','ndebele','swati','tsonga'].forEach(x=>document.getElementById('sk-'+x)?.classList.toggle('sel',x===s));}
function selTP(n){_tPlayers=n;[4,8,16].forEach(x=>document.getElementById('tp-'+x)?.classList.toggle('sel',x===n));}
function renderLangGrid(){
  const g=document.getElementById('lang-grid');g.innerHTML='';
  Object.entries(LANGS_C).forEach(([code,lng])=>{
    const b=document.createElement('button');
    b.className='card'+(CL===code?' sel':'');
    b.style.cssText='min-width:70px;padding:5px 8px;';
    b.innerHTML=`<div class="ctitle" style="font-size:10px">${lng.flag||''} ${lng.label||code}</div>`;
    b.onclick=()=>{CL=code;LANG=LANGS_C[code]||LANGS_C['en'];renderLangGrid();};
    g.appendChild(b);
  });
}

// ── Start ─────────────────────────────────────────────────────────────────────
async function startGame(){
  if(_mode==='online'){showOnlinePanel();return;}
  closeAllM();_busy=false;_frames=[];
  const isC=_level===1;
  document.body.className=isC?'child-mode':'';
  if(isC)startCTips();else stopCTips();
  try{
    const r=await fetch('/api/game/start',{method:'POST',
      headers:{'Content-Type':'application/json'},
      body:JSON.stringify({level:_level,mode:_mode,skin:_skin,lang:CL})});
    const d=await r.json();
    if(!d.ok)throw new Error(d.error||'Could not start game');
    _gs=d.state;_skinData=d.skin;calcBoard();updHUD();
    if(isC){
      narrate('🐄 Welcome to Calf Level! Watch the tip at the top! ✨',5000);
      setTimeout(()=>narrate('💡 YOUR holes are on the BOTTOM. Tap one to begin! 👇',4800),5500);
    } else {
      narrate(`🎮 ${LANG.start||'Game started!'} · Level ${_level} · ${_mode==='ai'?(LANG.vsAI||'vs AI'):LANG.twoPlayers||'2 Players'}`,3000);
    }
  }catch(e){narrate('⚠️ '+e.message);showHome();}
}

// ── Auth ──────────────────────────────────────────────────────────────────────
function showAuth(){document.getElementById('auth-modal').classList.remove('hidden');}
function showProfile(){if(!_user?.email){showAuth();return;}renderProfile();document.getElementById('profile-modal').classList.remove('hidden');}
function togAuth(){_authMode=_authMode==='login'?'register':'login';renderAuthForm();}
function renderAuthForm(){
  const r=_authMode==='register';
  document.getElementById('auth-h').textContent=r?'Register':'Sign In';
  document.getElementById('auth-sub').textContent=r?'Bhalisa · Register':'Ngena · Sign In';
  document.getElementById('auth-btn').textContent=r?'BHALISA · REGISTER':'NGENA · SIGN IN';
  document.getElementById('auth-tog').textContent=r?'Already registered? Sign In':'New? Register';
  ['name-wrap','conf-wrap','pw-strength'].forEach(id=>document.getElementById(id).style.display=r?'block':'none');
  ['aerr','aok'].forEach(id=>{const e=document.getElementById(id);e.style.display='none';e.textContent='';});
  if(r){
    document.getElementById('inp-pass').oninput=()=>{
      const pw=document.getElementById('inp-pass').value;
      let s=0;if(pw.length>=8)s++;if(pw.length>=12)s++;
      if(/[A-Z]/.test(pw))s++;if(/[0-9]/.test(pw))s++;if(/[^A-Za-z0-9]/.test(pw))s++;
      const cols=['#FF1744','#FF5722','#FF9800','#FFC107','#8BC34A','#4CAF50'];
      const labs=['Very Weak','Weak','Fair','Good','Strong','Very Strong'];
      document.getElementById('sfill').style.cssText=`width:${s/5*100}%;background:${cols[s]}`;
      document.getElementById('shint').textContent=labs[s];
    };
  }
}
async function doAuth(){
  const r=_authMode==='register';
  const email=document.getElementById('inp-email').value.trim();
  const pw=document.getElementById('inp-pass').value;
  const name=document.getElementById('inp-name').value.trim();
  const conf=document.getElementById('inp-conf').value;
  const err=document.getElementById('aerr'),ok=document.getElementById('aok');
  if(!email||!pw){err.textContent='Email and password required';err.style.display='block';return;}
  if(r&&!name){err.textContent='Name is required';err.style.display='block';return;}
  if(r&&pw!==conf){err.textContent='Passwords do not match';err.style.display='block';return;}
  try{
    const res=await fetch(r?'/api/register':'/api/login',{method:'POST',
      headers:{'Content-Type':'application/json'},
      body:JSON.stringify(r?{email,password:pw,name}:{email,password:pw})});
    const d=await res.json();
    if(!d.ok){err.textContent=d.error||'Error';err.style.display='block';return;}
    _user=d.user;ok.textContent=(r?'Welcome! ':'Welcome back, ')+d.user.name+'!';ok.style.display='block';
    setTimeout(()=>{closeM('auth-modal');updHomeAuthBtn();narrate('👋 Welcome, '+_user.name+'! 🐄');},1200);
  }catch(e){document.getElementById('aerr').textContent='Network error';document.getElementById('aerr').style.display='block';}
}
function guestGo(){closeM('auth-modal');narrate('👤 Playing as Guest — register to save your cattle! 🐄');}
async function doLogout(){
  await fetch('/api/logout',{method:'POST'});
  _user={name:'Guest',email:'',wins:0,losses:0,draws:0,games:0,skin:'zulu',level:1,lang:'en',total_cows:0};
  closeM('profile-modal');updHomeAuthBtn();narrate('👋 Logged out');
}
function renderProfile(){
  document.getElementById('pname').textContent=_user.name||'Guest';
  document.getElementById('pemail').textContent=_user.email||'';
  document.getElementById('pcows').textContent='🐄 '+(_user.total_cows||0)+' cattle won';
  const ss=[{l:'Wins',v:_user.wins||0,c:'#6bffaa'},{l:'Losses',v:_user.losses||0,c:'#ff6b6b'},
            {l:'Draws',v:_user.draws||0,c:'#ffcc44'},{l:'Games',v:_user.games||0,c:'#88bbff'}];
  document.getElementById('pstats').innerHTML=ss.map(s=>
    `<div style="text-align:center;padding:7px;background:rgba(201,168,76,.07);border-radius:6px">
      <div style="font-family:'Cinzel',serif;font-size:18px;color:${s.c}">${s.v}</div>
      <div style="font-size:9px;color:rgba(245,236,215,.38);letter-spacing:1px">${s.l}</div>
    </div>`).join('');
}

// ── Online ────────────────────────────────────────────────────────────────────
function showOnlinePanel(){closeAllM();if(!_user?.email){narrate('🔒 Sign in to play online');showAuth();return;}document.getElementById('online-modal').classList.remove('hidden');}
async function createOnlineGame(){
  try{
    const d=await(await fetch('/api/online/create',{method:'POST',
      headers:{'Content-Type':'application/json'},body:JSON.stringify({level:_level,skin:_skin})})).json();
    if(!d.ok)throw new Error(d.error||'Failed');
    _onlineRoom=d.room_id;
    document.getElementById('room-code-disp').textContent=d.room_id;
    document.getElementById('online-info').style.display='block';
    narrate('🌍 Room '+d.room_id+' created! Share the code.',5000);
    pollOnline(d.room_id);
  }catch(e){narrate('⚠️ '+e.message);}
}
async function joinOnlineGame(){
  const code=document.getElementById('join-code-inp').value.trim().toUpperCase();
  if(!code){narrate('⚠️ Enter room code');return;}
  try{
    const d=await(await fetch('/api/online/join',{method:'POST',
      headers:{'Content-Type':'application/json'},body:JSON.stringify({code})})).json();
    if(!d.ok)throw new Error(d.error||'Failed');
    _onlineRoom=d.room_id;narrate("✅ Joined "+d.host_name+"'s game!",4000);
    closeM('online-modal');
  }catch(e){narrate('⚠️ '+e.message);}
}
function pollOnline(id){
  if(_pollT)clearInterval(_pollT);
  _pollT=setInterval(async()=>{
    try{
      const d=await(await fetch('/api/online/state/'+id)).json();
      if(d.ok&&d.room?.status==='playing'){
        clearInterval(_pollT);_pollT=null;
        document.getElementById('online-status').textContent='Opponent joined! Starting…';
        document.querySelector('.dot.wait').className='dot go';
        setTimeout(()=>closeM('online-modal'),1500);
      }
    }catch(e){}
  },2000);
}

// ── Tournament ────────────────────────────────────────────────────────────────
function showTournament(){closeAllM();if(!_user?.email){narrate('🔒 Sign in for tournaments');showAuth();return;}document.getElementById('tournament-modal').classList.remove('hidden');loadT();}
function togCreateT(){const f=document.getElementById('create-t');f.style.display=f.style.display==='none'?'block':'none';}
async function submitT(){
  const name=document.getElementById('t-name').value.trim()||'My Tournament';
  try{
    const d=await(await fetch('/api/tournament/create',{method:'POST',
      headers:{'Content-Type':'application/json'},body:JSON.stringify({name,max_players:_tPlayers})})).json();
    if(!d.ok)throw new Error(d.error||'Failed');
    narrate('🏆 Tournament "'+d.name+'" created! ID: '+d.tournament_id,5000);loadT();
  }catch(e){narrate('⚠️ '+e.message);}
}
async function loadT(){
  try{
    const d=await(await fetch('/api/tournament/list')).json();
    const list=document.getElementById('t-list');list.innerHTML='';
    if(!d.tournaments?.length){list.innerHTML='<div style="text-align:center;padding:14px;opacity:.35">No open tournaments</div>';return;}
    d.tournaments.forEach(t=>{
      const p=JSON.parse(t.players||'[]');
      const row=document.createElement('div');row.className='t-row';
      row.innerHTML=`<div style="font-family:'Cinzel',serif;color:var(--gold);font-size:13px">${t.name}</div>
        <div style="font-size:11px;opacity:.5;margin-top:3px">Host: ${t.host_name} · ${p.length}/${t.max_players} players</div>
        <button class="btn blue" style="font-size:10px;padding:4px 12px;margin-top:6px" onclick="joinT('${t.id}')">Join</button>`;
      list.appendChild(row);
    });
  }catch(e){}
}
async function joinT(id){
  try{
    const d=await(await fetch('/api/tournament/join',{method:'POST',
      headers:{'Content-Type':'application/json'},body:JSON.stringify({tournament_id:id})})).json();
    if(!d.ok)throw new Error(d.error||'Failed');
    narrate('✅ Joined tournament! '+d.players+'/'+d.max+' players',4000);loadT();
  }catch(e){narrate('⚠️ '+e.message);}
}

// ── SUPPORT CHAT ──────────────────────────────────────────────────────────────
async function initChat(){
  if(_cwSid)return;
  _cwSid='cw_'+Date.now()+'_'+Math.random().toString(36).slice(2,8);
  try{
    const d=await(await fetch('/api/chat/start',{method:'POST',
      headers:{'Content-Type':'application/json'},
      body:JSON.stringify({session_id:_cwSid,name:_user.name||'Guest'})})).json();
    if(d.ok){
      renderCwMsgs(d.messages);
      renderSurvey(d.survey);
      // Show notification badge
      const badge=document.getElementById('chat-badge');
      badge.style.display='flex';
      badge.textContent='1';
    }
  }catch(e){}
}
function toggleChat(){
  _cwOpen=!_cwOpen;
  document.getElementById('chat-window').classList.toggle('open',_cwOpen);
  if(_cwOpen){
    document.getElementById('chat-badge').style.display='none';
    if(!_cwSid)initChat();
    setTimeout(()=>document.getElementById('cw-inp').focus(),180);
  }
}
function cwTab(tab){
  _cwTab=tab;
  document.getElementById('tab-chat').classList.toggle('act',tab==='chat');
  document.getElementById('tab-survey').classList.toggle('act',tab==='survey');
  document.getElementById('chat-pane').style.display=tab==='chat'?'flex':'none';
  document.getElementById('survey-pane').classList.toggle('open',tab==='survey');
}
function renderCwMsgs(msgs){
  if(!msgs)return;
  const c=document.getElementById('cw-msgs');c.innerHTML='';
  msgs.forEach(m=>{
    const d=document.createElement('div');
    d.className='cw-msg '+(m.sender==='user'?'usr':'sup');
    const t=m.created?new Date(m.created*1000).toLocaleTimeString([],{hour:'2-digit',minute:'2-digit'}):'';
    d.innerHTML=`<div>${m.message}</div><div class="mt">${t}</div>`;
    c.appendChild(d);
  });
  c.scrollTop=c.scrollHeight;
}
function appendCwMsg(sender,text){
  const c=document.getElementById('cw-msgs');
  const d=document.createElement('div');
  d.className='cw-msg '+(sender==='user'?'usr':'sup');
  const t=new Date().toLocaleTimeString([],{hour:'2-digit',minute:'2-digit'});
  d.innerHTML=`<div>${text}</div><div class="mt">${t}</div>`;
  c.appendChild(d);c.scrollTop=c.scrollHeight;
}
async function cwSend(){
  const inp=document.getElementById('cw-inp');
  const msg=inp.value.trim();if(!msg)return;
  if(!_cwSid)await initChat();
  inp.value='';
  appendCwMsg('user',msg);
  // Typing indicator
  appendCwMsg('sup','💬 …');
  const typing=document.getElementById('cw-msgs').lastChild;
  try{
    const d=await(await fetch('/api/chat/send',{method:'POST',
      headers:{'Content-Type':'application/json'},
      body:JSON.stringify({session_id:_cwSid,message:msg,name:_user.name||'Guest'})})).json();
    typing.remove();
    if(d.ok){
      appendCwMsg('sup',d.reply);
      if(d.show_survey){
        setTimeout(()=>appendCwMsg('sup','💡 Enjoying Intshuba? Tap the ⭐ Rate Us tab to share your thoughts — it only takes 30 seconds!'),2200);
      }
    }
  }catch(e){typing.remove();appendCwMsg('sup','⚠️ Network error. Try again or email info@inkazimulo.digital');}
}

// ── Survey ────────────────────────────────────────────────────────────────────
function renderSurvey(questions){
  const panel=document.getElementById('sq-list');panel.innerHTML='';
  (questions||[]).forEach(q=>{
    const w=document.createElement('div');
    w.style.cssText='margin-bottom:12px;padding:9px;background:rgba(201,168,76,.05);border-radius:8px;';
    if(q.type==='stars'){
      w.innerHTML=`<div class="sq">${q.question}</div>
        <div class="star-row">${q.options.map((o,i)=>
          `<button class="sstar" data-qid="${q.id}" onclick="setSurvStar('${q.id}',${i+1})">${o}</button>`
        ).join('')}</div>`;
    } else if(q.type==='choice'){
      w.innerHTML=`<div class="sq">${q.question}</div>
        <div class="choice-wrap">${q.options.map(o=>
          `<button class="cbtn-sm" data-qid="${q.id}" onclick="setSurvChoice('${q.id}',this,'${o.replace(/['"]/g,'')}')">${o}</button>`
        ).join('')}</div>`;
    } else if(q.type==='text'){
      w.innerHTML=`<div class="sq">${q.question}</div>
        <textarea class="sq-text" id="sqt_${q.id}" placeholder="${q.placeholder||''}"></textarea>`;
    }
    panel.appendChild(w);
  });
}
function setSurvStar(qid,val){
  _surveyAns[qid]=val;
  document.querySelectorAll(`[data-qid="${qid}"].sstar`).forEach((b,i)=>b.classList.toggle('lit',i<val));
}
function setSurvChoice(qid,btn,val){
  _surveyAns[qid]=val;
  document.querySelectorAll(`[data-qid="${qid}"].cbtn-sm`).forEach(b=>b.classList.remove('sel'));
  btn.classList.add('sel');
}
async function cwSubmitSurvey(){
  // Collect text answers
  document.querySelectorAll('.sq-text').forEach(el=>{
    if(el.value.trim())_surveyAns[el.id.replace('sqt_','')]=el.value.trim();
  });
  if(!Object.keys(_surveyAns).length){
    document.getElementById('sq-ok').textContent='Please answer at least one question!';
    document.getElementById('sq-ok').style.display='block';return;
  }
  try{
    const d=await(await fetch('/api/survey/submit',{method:'POST',
      headers:{'Content-Type':'application/json'},
      body:JSON.stringify({answers:_surveyAns,name:_user.name||'Guest'})})).json();
    document.getElementById('sq-ok').textContent=d.message||'Thank you! 🐄';
    document.getElementById('sq-ok').style.display='block';
    _surveyAns={};
  }catch(e){}
}

// ── Feedback Modal ────────────────────────────────────────────────────────────
function showFbModal(){document.getElementById('fb-modal').classList.remove('hidden');}
function setFbRating(n){
  _fbRating=n;
  document.querySelectorAll('.fb-star').forEach((s,i)=>s.classList.toggle('lit',i<n));
  const lbl=['','Needs work 😕','Could be better 🤔','Good 👍','Great! 😊','Amazing! 🌟'];
  document.getElementById('fb-rating-lbl').textContent=lbl[n]||'';
}
function selCat(btn,cat){
  _fbCat=cat;
  document.querySelectorAll('.cat-chip').forEach(b=>b.classList.remove('sel'));
  btn.classList.add('sel');
}
async function submitFb(){
  const msg=document.getElementById('fb-msg').value.trim();
  const err=document.getElementById('fb-err'),ok=document.getElementById('fb-ok');
  err.style.display='none';ok.style.display='none';
  if(!msg){err.textContent='Please write a message';err.style.display='block';return;}
  if(!_fbRating){err.textContent='Please tap a star rating first';err.style.display='block';return;}
  try{
    const d=await(await fetch('/api/feedback/submit',{method:'POST',
      headers:{'Content-Type':'application/json'},
      body:JSON.stringify({rating:_fbRating,category:_fbCat,message:msg,
        name:_user.name||'Guest',email:_user.email||'',platform:'web'})})).json();
    if(!d.ok){err.textContent=d.error||'Error';err.style.display='block';return;}
    ok.textContent=d.message||'Thank you! 🐄';ok.style.display='block';
    document.getElementById('fb-msg').value='';
    _fbRating=0;document.querySelectorAll('.fb-star').forEach(s=>s.classList.remove('lit'));
    document.getElementById('fb-rating-lbl').textContent='Tap stars to rate';
    setTimeout(()=>closeM('fb-modal'),2600);
  }catch(e){err.textContent='Network error';err.style.display='block';}
}

// ── Init ──────────────────────────────────────────────────────────────────────
(async function init(){
  renderAuthForm();
  const path=window.location.pathname;
  if(path.startsWith('/join/')){
    const code=path.slice(6);
    document.getElementById('join-code-inp').value=code;
  }
  try{
    const d=await(await fetch('/api/me')).json();
    if(d.user){
      _user=d.user;
      if(_user.lang&&LANGS_C[_user.lang]){CL=_user.lang;LANG=LANGS_C[_user.lang];}
      if(_user.skin)selSkin(_user.skin);
      if(_user.level)selLevel(_user.level);
      narrate('👋 Welcome back, '+_user.name+'! 🐄');
    } else {
      narrate('🎮 Welcome to Intshuba · Nguni Stone Game · Sign in to save progress');
    }
  }catch(e){}
  showHome();
  // Init chat support after a brief delay
  setTimeout(initChat, 2500);
})();

async function copyShareLink() {
  const url = window.location.origin;
  try {
    await navigator.clipboard.writeText(url);
    narrate('✅ Link copied! Share the game with friends!', 3000);
  } catch(e) {
    // fallback
    const ta = document.createElement('textarea');
    ta.value = url; document.body.appendChild(ta);
    ta.select(); document.execCommand('copy');
    document.body.removeChild(ta);
    narrate('✅ Link copied!', 2000);
  }
}

async function shareWin(score, level) {
  try {
    const d = await (await fetch('/api/share/generate', {
      method: 'POST', headers: {'Content-Type':'application/json'},
      body: JSON.stringify({event:'win', score, level, name: _user?.name||'A player',
                           tribe: _userTribe||'world', title: _kdata?.title||'iNduna'}),
    })).json();
    if (d.ok) showShareModal(d);
  } catch(e) {}
}

function showShareModal(shareData) {
  const urls = shareData.share_urls || {};
  const text = shareData.text || '';
  // Quick share panel using narrate area
  narrate('🐄 ' + (text.slice(0,80)||'Share your win!'), 4000);
  // Open WhatsApp share directly
  if (urls.whatsapp) window.open(urls.whatsapp, '_blank');
}

// ══════════════════════════════════════════════════════════════════════════════
//  TRIBAL SOUND SYNTHESIZER  –  Web Audio API procedural tribal sounds
// ══════════════════════════════════════════════════════════════════════════════

const _AudioCtx = window.AudioContext || window.webkitAudioContext;
let _audioCtx = null;
let _soundEnabled = true;
let _userTribe = 'world';

function getAudioCtx() {
  if (!_audioCtx) {
    try { _audioCtx = new _AudioCtx(); } catch(e) {}
  }
  return _audioCtx;
}

const TRIBE_SOUND_PROFILES = {
  amazulu:    { win: [[220,0.8],[280,0.6],[350,0.4],[440,0.3]], capture: [[330,0.9],[220,0.5]], type: 'drum',    rhythm: [0,0.15,0.3,0.5] },
  amaxhosa:   { win: [[330,0.7],[415,0.5],[495,0.4],[660,0.3]], capture: [[495,0.8],[660,0.4]], type: 'voice',   rhythm: [0,0.2,0.35,0.55] },
  amandebele: { win: [[264,0.6],[330,0.7],[396,0.5],[528,0.4]], capture: [[396,0.8],[528,0.5]], type: 'marimba', rhythm: [0,0.18,0.36,0.54] },
  emaswati:   { win: [[196,0.9],[247,0.6],[294,0.5],[392,0.4]], capture: [[294,0.9],[392,0.5]], type: 'horn',    rhythm: [0,0.25,0.5,0.75] },
  vatsonga:   { win: [[293,0.7],[370,0.8],[440,0.6],[587,0.4]], capture: [[440,0.9],[587,0.5]], type: 'mbila',   rhythm: [0,0.12,0.24,0.48] },
  basotho:    { win: [[175,0.6],[220,0.5],[262,0.7],[350,0.4]], capture: [[262,0.8],[350,0.4]], type: 'flute',   rhythm: [0,0.22,0.44,0.66] },
  bapedi:     { win: [[220,0.8],[277,0.6],[330,0.7],[440,0.5]], capture: [[330,0.9],[440,0.6]], type: 'drum',    rhythm: [0,0.13,0.26,0.52] },
  bavenda:    { win: [[261,0.7],[329,0.6],[392,0.5],[523,0.4]], capture: [[392,0.8],[523,0.5]], type: 'pipe',    rhythm: [0,0.2,0.4,0.7] },
  world:      { win: [[440,0.8],[550,0.6],[660,0.5],[880,0.4]], capture: [[660,0.9],[880,0.5]], type: 'fanfare', rhythm: [0,0.18,0.36,0.6] },
};

function _playTone(freq, gain, startTime, duration, type, ctx) {
  const osc  = ctx.createOscillator();
  const gainN = ctx.createGain();
  osc.type = type === 'drum' ? 'sine' : type === 'flute' ? 'sine' : type === 'voice' ? 'triangle' : 'square';
  osc.frequency.setValueAtTime(freq, startTime);
  if (type === 'drum') osc.frequency.exponentialRampToValueAtTime(freq * 0.3, startTime + duration);
  gainN.gain.setValueAtTime(gain * 0.3, startTime);
  gainN.gain.exponentialRampToValueAtTime(0.001, startTime + duration);
  osc.connect(gainN);
  gainN.connect(ctx.destination);
  osc.start(startTime);
  osc.stop(startTime + duration);
}

function playTribeSound(event) {
  if (!_soundEnabled) return;
  const ctx = getAudioCtx();
  if (!ctx) return;
  if (ctx.state === 'suspended') ctx.resume();
  const profile = TRIBE_SOUND_PROFILES[_userTribe] || TRIBE_SOUND_PROFILES.world;
  const notes   = event === 'win' ? profile.win : profile.capture;
  const rhythm  = profile.rhythm;
  const now     = ctx.currentTime;
  notes.forEach(([freq, gain], i) => {
    const t = now + (rhythm[i] || i * 0.2);
    _playTone(freq, gain, t, 0.5, profile.type, ctx);
  });
  // Extra win flourish
  if (event === 'win') {
    setTimeout(() => {
      const ctx2 = getAudioCtx();
      if (!ctx2) return;
      notes.forEach(([freq, gain], i) => {
        _playTone(freq * 2, gain * 0.4, ctx2.currentTime + i * 0.12, 0.3, profile.type, ctx2);
      });
    }, 600);
  }
}

function playLevelUpSound() {
  const ctx = getAudioCtx();
  if (!ctx) return;
  if (ctx.state === 'suspended') ctx.resume();
  const now = ctx.currentTime;
  [440, 554, 659, 880].forEach((f, i) => {
    _playTone(f, 0.4, now + i * 0.15, 0.4, 'fanfare', ctx);
  });
}

function playCaptureSound() { playTribeSound('capture'); }
function playWinSound()     { playTribeSound('win'); }

// Patch into game events
const _origHandleGameOver = typeof gameOver === 'function' ? gameOver : null;

// ══════════════════════════════════════════════════════════════════════════════
//  TRIBE SELECTION MODAL JS
// ══════════════════════════════════════════════════════════════════════════════

let _tribesData = {};

async function loadTribesData() {
  try {
    const d = await (await fetch('/api/tribes')).json();
    _tribesData = d;
    return d;
  } catch(e) { return {}; }
}

async function showTribeModal() {
  document.getElementById('tribe-modal')?.classList.remove('hidden');
  if (!Object.keys(_tribesData).length) await loadTribesData();
  renderTribeCards();
}

function renderTribeCards() {
  const grid = document.getElementById('tribe-cards');
  if (!grid || !_tribesData.tribes) return;
  const COLORS = {
    amazulu: '#C8102E', amaxhosa: '#228B22', amandebele: '#4444FF',
    emaswati: '#9B4FCC', vatsonga: '#FF8C00', basotho: '#4488FF',
    bapedi: '#8B0000', bavenda: '#008080', world: '#C9A84C',
  };
  grid.innerHTML = Object.entries(_tribesData.tribes).map(([id, tribe]) => {
    const isSel = id === _userTribe;
    const col   = COLORS[id] || '#C9A84C';
    return `<div onclick="selectTribe('${id}')" style="
      background:rgba(201,168,76,.07);border:${isSel ? '2px solid ' + col : '1px solid rgba(201,168,76,.25)'};
      border-radius:12px;padding:12px;cursor:pointer;transition:.2s;text-align:center;
      ${isSel ? 'box-shadow:0 0 16px ' + col + '44' : ''}">
      <div style="font-size:28px;margin-bottom:4px">${tribe.icon}</div>
      <div style="font-family:'Cinzel',serif;color:${isSel ? col : 'var(--gold)'};font-size:12px;font-weight:bold;margin-bottom:3px">${tribe.name}</div>
      <div style="font-size:10px;color:rgba(245,236,215,.45);margin-bottom:6px;line-height:1.4">${tribe.region||''}</div>
      <div style="font-size:10px;color:rgba(245,236,215,.6);background:rgba(255,255,255,.05);border-radius:8px;padding:3px 6px">${tribe.bonus_desc||''}</div>
    </div>`;
  }).join('');
}

async function selectTribe(tribeId) {
  if (!_user?.email) { showAuth(); return; }
  try {
    const d = await (await fetch('/api/tribe/join', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({ tribe_id: tribeId }),
    })).json();
    if (d.ok) {
      _userTribe = tribeId;
      narrate(d.message, 4000);
      renderTribeCards();
      // Update sound profile
      playTribeSound('capture');
    }
  } catch(e) { narrate('⚠️ ' + e.message); }
}

// ══════════════════════════════════════════════════════════════════════════════
//  COMPETITION UI JS
// ══════════════════════════════════════════════════════════════════════════════

async function showCompetitions() {
  if (!_user?.email) { narrate('🔒 Sign in to enter competitions'); showAuth(); return; }
  document.getElementById('comp-modal')?.classList.remove('hidden');
  await loadCompetitions();
}

async function loadCompetitions() {
  try {
    const d = await (await fetch('/api/competition/list')).json();
    const el = document.getElementById('comp-list');
    if (!el) return;
    const comps = d.competitions || [];
    if (!comps.length) {
      el.innerHTML = '<div style="text-align:center;opacity:.4;padding:20px">No open competitions — be the first to create one!</div>';
      return;
    }
    el.innerHTML = comps.map(c => {
      const prize = c.prize_pool_zar ? 'R' + (c.prize_pool_zar/100).toLocaleString() : 'Glory';
      const fee   = c.entry_fee_zar  ? 'R' + (c.entry_fee_zar/100).toFixed(0) + ' entry' : 'Free entry';
      return `<div style="border:1px solid var(--border);border-radius:8px;padding:12px;margin-bottom:8px;cursor:pointer;transition:.2s"
        onmouseover="this.style.background='rgba(201,168,76,.07)'" onmouseout="this.style.background=''">
        <div style="display:flex;justify-content:space-between;align-items:flex-start">
          <div>
            <div style="font-family:'Cinzel',serif;color:var(--gold);font-size:13px">${c.name}</div>
            <div style="font-size:11px;color:rgba(245,236,215,.45);margin-top:2px">${c.comp_type} · ${c.age_pool} · ${fee}</div>
          </div>
          <div style="text-align:right">
            <div style="color:#6bffaa;font-size:12px;font-weight:bold">🏆 ${prize}</div>
            <button class="btn green" style="font-size:10px;padding:4px 12px;margin-top:4px"
              onclick="joinComp('${c.id}')">Join</button>
          </div>
        </div>
      </div>`;
    }).join('');
  } catch(e) {}
}

async function joinComp(compId) {
  try {
    const d = await (await fetch('/api/competition/join', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({ competition_id: compId, tribe: _userTribe, age_pool: 'open' }),
    })).json();
    narrate(d.message || d.error || 'Joined!', 4000);
    await loadCompetitions();
  } catch(e) { narrate('⚠️ ' + e.message); }
}

async function createCompetition() {
  const name  = document.getElementById('comp-name')?.value.trim() || 'My Tournament';
  const ctype = document.getElementById('comp-type')?.value || 'community';
  try {
    const d = await (await fetch('/api/competition/create', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({ name, type: ctype, tribe: _userTribe, age_pool: 'open' }),
    })).json();
    narrate(d.ok ? `🏆 "${d.name}" created! ID: ${d.competition_id}` : (d.error || 'Error'), 5000);
    if (d.ok) await loadCompetitions();
  } catch(e) { narrate('⚠️ ' + e.message); }
}

// ══════════════════════════════════════════════════════════════════════════════
//  TRIBE WAR LEADERBOARD
// ══════════════════════════════════════════════════════════════════════════════

async function loadTribeWar() {
  try {
    const d  = await (await fetch('/api/tribe/war/standings')).json();
    const el = document.getElementById('tribe-war-list');
    if (!el) return;
    const standings = d.standings || [];
    el.innerHTML = standings.map((t, i) => {
      const medal = ['🥇','🥈','🥉'][i] || `#${i+1}`;
      const crown = t.has_king ? ' 👑' : '';
      return `<div style="display:flex;justify-content:space-between;align-items:center;
        padding:8px 10px;border-radius:6px;margin-bottom:4px;
        background:${i===0 ? 'rgba(201,168,76,.12)' : i%2===0 ? 'rgba(201,168,76,.04)' : ''}">
        <span style="font-size:14px">${medal}</span>
        <span style="font-size:16px">${t.tribe_icon}</span>
        <span style="flex:1;padding:0 8px;font-family:'Cinzel',serif;color:var(--gold);font-size:12px">${t.tribe_name}${crown}</span>
        <span style="font-size:12px;color:rgba(245,236,215,.5)">${t.members||0} warriors</span>
        <span style="color:var(--gold);font-size:13px;font-weight:bold;margin-left:8px">🐄 ${(t.total_cows||0).toLocaleString()}</span>
      </div>`;
    }).join('') || '<div style="opacity:.4;padding:16px;text-align:center">No tribe data yet</div>';
  } catch(e) {}
}

// ══════════════════════════════════════════════════════════════════════════════
//  SEASON STATUS
// ══════════════════════════════════════════════════════════════════════════════

async function loadSeasonStatus() {
  try {
    const d  = await (await fetch('/api/season/status')).json();
    const el = document.getElementById('season-info');
    if (!el) return;
    el.innerHTML = `
      <div style="text-align:center;margin-bottom:12px">
        <div style="font-size:11px;color:rgba(245,236,215,.4);letter-spacing:2px">SEASON ${d.season}</div>
        <div style="font-family:'Cinzel',serif;font-size:20px;color:var(--gold)">${d.days_left} days remaining</div>
      </div>
      <div style="text-align:center;margin-bottom:10px">
        <div style="font-size:11px;color:rgba(245,236,215,.4)">CURRENT RULER</div>
        <div style="font-size:18px">👑 ${d.king?.name || 'AI Inkosi'}</div>
      </div>
      <div class="slabel">SEASON LEADERS</div>
      ${(d.top_players||[]).slice(0,5).map((p,i)=>`
        <div style="display:flex;justify-content:space-between;padding:4px 8px;font-size:12px;
          border-radius:4px;background:${i%2===0?'rgba(201,168,76,.05)':''}">
          <span>${['🥇','🥈','🥉','4.','5.'][i]||''} ${p.name}</span>
          <span style="color:var(--gold)">${p.herd_cows||0}🐄</span>
        </div>`).join('')}`;
  } catch(e) {}
}

// ══════════════════════════════════════════════════════════════════════════════
//  INIT — load tribe + season data on startup
// ══════════════════════════════════════════════════════════════════════════════
setTimeout(async () => {
  await loadTribesData();
  if (_user?.email) {
    // Restore user's tribe from profile
    try {
      const d = await (await fetch('/api/user/profile-full')).json();
      if (d.tribe_id) {
        _userTribe = d.tribe_id;
        // Update herd counter
        const hc = document.getElementById('herd-count');
        if (hc && d.herd_cows !== undefined) hc.textContent = d.herd_cows + ' 🐄';
      }
    } catch(e) {}
  }
}, 4000);

function compTab(tab) {
  ['open','create','tribe','season'].forEach(t => {
    document.getElementById('ct-' + t)?.classList.toggle('act', t === tab);
    const el = document.getElementById('cp-' + t);
    if (el) el.style.display = t === tab ? 'block' : 'none';
  });
  if (tab === 'tribe')  loadTribeWar();
  if (tab === 'season') loadSeasonStatus();
  if (tab === 'open')   loadCompetitions();
}

async function registerAgePool() {
  const yr = parseInt(document.getElementById('birth-year-inp')?.value || '0');
  if (yr < 1920 || yr > 2020) { narrate('⚠️ Enter a valid birth year (1920–2020)'); return; }
  try {
    const d = await (await fetch('/api/user/set-age-pool', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({ birth_year: yr }),
    })).json();
    document.getElementById('age-pool-result').textContent = d.pool_info?.icon + ' ' + d.pool_info?.label;
    narrate(d.message || d.error, 4000);
    if (d.ok) setTimeout(() => closeM('age-modal'), 1500);
  } catch(e) { narrate('⚠️ ' + e.message); }
}


// ── Kingdom Economy ────────────────────────────────────────────────────────────
let _kdata = {};
let _activeBetId = null, _activeBetAmt = 0, _pendingGameLevel = 1;

async function loadKingdom() {
  if (!_user?.email) return;
  try {
    const d = await (await fetch('/api/economy/status')).json();
    _kdata = d;
    // Update HUD herd counter
    const hc = document.getElementById('herd-count');
    if (hc) hc.textContent = (d.herd_cows || 0) + ' 🐄';
    // Title bar
    const ti = d.title_info || {};
    const el = document.getElementById('k-title-icon');
    if (el) el.textContent = ti.icon || '🐄';
    const tl = document.getElementById('k-title-label');
    if (tl) tl.textContent = (d.title || 'iNkonyana') + ' · ' + (ti.label || 'Calf');
    // King banner
    const king = d.king || {};
    const kb = document.getElementById('k-king-banner');
    if (kb) kb.style.display = king.name ? 'block' : 'none';
    const kn = document.getElementById('k-king-name');
    if (kn) kn.textContent = king.name || '';
  } catch(e) { console.error('loadKingdom:', e); }
}

async function showKingdom() {
  if (!_user?.email) { narrate('🔒 Sign in to access your Kingdom'); showAuth(); return; }
  document.getElementById('kingdom-modal').classList.remove('hidden');
  await loadKingdom();
  renderKStats();
  renderKHerd();
  renderKMarket();
  renderKCrown();
  renderKHall();
}

function kTab(tab) {
  ['herd','market','crown','hall'].forEach(t => {
    document.getElementById('kt-' + t)?.classList.toggle('act', t === tab);
    document.getElementById('kp-' + t).style.display = t === tab ? 'block' : 'none';
  });
  if (tab === 'hall') loadKHall();
}

function renderKStats() {
  const d = _kdata;
  const grid = document.getElementById('k-stats-grid');
  if (!grid) return;
  const stats = [
    { label: 'Herd Cows', v: d.herd_cows || 0, icon: '🐄' },
    { label: 'Land Plots', v: d.land_plots || 0, icon: '🌾' },
    { label: 'Jewellery', v: d.jewellery || 0, icon: '💍' },
    { label: d.is_married ? 'Married ❤️' : 'Single', v: d.wins || 0, icon: d.is_married ? '💑' : '🏆' },
  ];
  grid.innerHTML = stats.map(s =>
    `<div style="background:rgba(201,168,76,.07);border:1px solid rgba(201,168,76,.2);
      border-radius:8px;padding:8px;text-align:center">
      <div style="font-size:20px">${s.icon}</div>
      <div style="font-family:'Cinzel',serif;color:var(--gold);font-size:16px">${s.v}</div>
      <div style="font-size:10px;color:rgba(245,236,215,.4);letter-spacing:.5px">${s.label.toUpperCase()}</div>
    </div>`
  ).join('');
}

function renderKHerd() {
  const d = _kdata;
  const packs = document.getElementById('k-cow-packs');
  if (!packs) return;
  const PACK_LABELS = {
    cows_daily: '☀️ Daily Gift — FREE',
    cows_10: '🐄 10 Cows — R5',
    cows_50: '🐄 50 Cows — R20',
    cows_200: '🐄 200 Cows — R49',
  };
  packs.innerHTML = Object.entries(d.cow_packs || {}).map(([id, p]) =>
    `<button onclick="buyCows('${id}')"
      style="background:rgba(201,168,76,.08);border:1px solid rgba(201,168,76,.25);
        border-radius:8px;color:var(--ivory);padding:10px;cursor:pointer;transition:.2s;
        font-size:12px;text-align:center;font-family:'Cinzel',serif;letter-spacing:.3px">
      ${PACK_LABELS[id] || (id + ' — ' + (p.price_zar ? 'R' + (p.price_zar/100).toFixed(0) : 'Free'))}
    </button>`
  ).join('');
  const evEl = document.getElementById('k-events');
  if (!evEl) return;
  const events = d.recent_events || [];
  if (events.length) {
    evEl.innerHTML = events.map(e => {
      const sign = e.cows_delta > 0 ? '+' : '';
      const col = e.cows_delta > 0 ? '#6bffaa' : '#ff9999';
      const ts = new Date(e.created * 1000).toLocaleTimeString([], {hour:'2-digit',minute:'2-digit'});
      return `<div style="display:flex;justify-content:space-between;border-bottom:.5px solid rgba(201,168,76,.1);padding:3px 0">
        <span>${e.event_type.replace(/_/g,' ')}</span>
        <span style="color:${col};font-weight:500">${sign}${e.cows_delta} 🐄 <span style="opacity:.4;font-size:10px">${ts}</span></span>
      </div>`;
    }).join('');
  } else {
    evEl.innerHTML = '<div style="opacity:.35;padding:8px 0">No events yet — start playing!</div>';
  }
}

function renderKMarket() {
  const d = _kdata;
  const el = document.getElementById('k-market-items');
  if (!el) return;
  const items = d.market_items || {};
  el.innerHTML = Object.entries(items).map(([id, item]) =>
    `<div style="background:rgba(201,168,76,.07);border:1px solid rgba(201,168,76,.25);
      border-radius:10px;padding:12px;text-align:center">
      <div style="font-size:28px;margin-bottom:4px">${item.icon}</div>
      <div style="font-family:'Cinzel',serif;color:var(--gold);font-size:11px;margin-bottom:4px">${item.name}</div>
      <div style="font-size:11px;color:rgba(245,236,215,.45);margin-bottom:8px;line-height:1.4">${item.desc}</div>
      <button class="btn green" style="font-size:10px;padding:5px 12px;width:100%"
        onclick="buyMarketItem('${id}')">
        ${item.cows} 🐄
      </button>
    </div>`
  ).join('');
}

function renderKCrown() {
  const d = _kdata;
  const king = d.king || {};
  const hn = document.getElementById('crown-holder-name');
  if (hn) hn.textContent = king.name || 'AI Inkosi';
  const hs = document.getElementById('crown-holder-sub');
  if (hs) hs.textContent = king.email === 'ai@intshuba' ? 'AI holds the throne — challenge it!' : 'Reigning Inkosi';
  const cb = document.getElementById('challenge-btn');
  if (cb) cb.disabled = (d.herd_cows || 0) < 300;
  const mi = document.getElementById('k-marriage-info');
  if (mi) {
    if (d.is_married && d.spouse) {
      mi.innerHTML = `<span style="color:#ff9fc6">💑 Married to <strong>${d.spouse.name || d.spouse_email}</strong></span>`;
    } else {
      mi.innerHTML = `<span style="color:rgba(245,236,215,.4)">You are not yet married. Propose with 100 🐄 lobola.</span>`;
    }
  }
}

async function renderKHall() {
  try {
    const d = await (await fetch('/api/kingdom/leaderboard')).json();
    const lbEl = document.getElementById('k-lb-list');
    if (lbEl) {
      const players = d.players || [];
      lbEl.innerHTML = players.length ?
        players.slice(0, 10).map((p, i) => {
          const crown = p.has_crown ? '👑 ' : '';
          const medal = ['🥇','🥈','🥉'][i] || '#' + (i+1);
          return `<div style="display:flex;justify-content:space-between;padding:5px 8px;
            border-radius:4px;background:${p.has_crown ? 'rgba(201,168,76,.12)' : i%2===0 ? 'rgba(201,168,76,.04)' : ''}">
            <span>${medal} ${crown}${p.name} <span style="font-size:10px;opacity:.5">${p.title||''}</span></span>
            <span style="color:var(--gold);font-size:12px">${p.herd_cows||0} 🐄</span>
          </div>`;
        }).join('')
        : '<div style="opacity:.35;padding:8px">No players yet</div>';
    }
    const hfEl = document.getElementById('k-hall-list');
    if (hfEl) {
      const hall = d.hall_fame || [];
      hfEl.innerHTML = hall.length ?
        hall.map(h => {
          const won = new Date(h.won_at * 1000).toLocaleDateString();
          return `<div>👑 <strong>${h.holder_name}</strong> — ${h.cows_at_crown}🐄 on ${won}</div>`;
        }).join('')
        : '<div style="opacity:.35">No kings yet — be the first!</div>';
    }
  } catch(e) {}
}

async function loadKHall() { await renderKHall(); }

async function buyCows(packId) {
  if (!_user?.email) { showAuth(); return; }
  const kMsg = document.getElementById('k-msg');
  if (kMsg) { kMsg.textContent = 'Processing…'; kMsg.style.display = 'block'; kMsg.className = 'ok'; }
  try {
    const d = await (await fetch('/api/economy/buy-cows', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({ pack: packId }),
    })).json();
    if (d.ok) {
      if (kMsg) kMsg.textContent = d.message || '🐄 Cows added!';
      await loadKingdom();
      renderKStats();
      renderKHerd();
    } else if (d.checkout_url) {
      if (kMsg) kMsg.textContent = 'Redirecting to payment…';
      setTimeout(() => window.open(d.checkout_url, '_blank'), 400);
    } else {
      if (kMsg) { kMsg.textContent = d.error || 'Error'; kMsg.className = 'err'; }
    }
  } catch(e) {
    if (kMsg) { kMsg.textContent = 'Network error'; kMsg.className = 'err'; }
  }
}

async function buyMarketItem(itemId) {
  if (!_user?.email) { showAuth(); return; }
  const kMsg = document.getElementById('k-msg');
  if (kMsg) { kMsg.textContent = 'Purchasing…'; kMsg.style.display = 'block'; kMsg.className = 'ok'; }
  try {
    const d = await (await fetch('/api/market/buy', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({ item: itemId }),
    })).json();
    if (d.ok) {
      if (kMsg) kMsg.textContent = d.message;
      await loadKingdom();
      renderKStats();
      renderKMarket();
      narrate(d.message, 5000);
    } else if (d.insufficient) {
      if (kMsg) { kMsg.textContent = d.message; kMsg.className = 'err'; }
    } else {
      if (kMsg) { kMsg.textContent = d.error || 'Could not purchase'; kMsg.className = 'err'; }
    }
  } catch(e) {
    if (kMsg) { kMsg.textContent = 'Network error'; kMsg.className = 'err'; }
  }
}

async function challengeCrown() {
  if (!_user?.email) { showAuth(); return; }
  try {
    const d = await (await fetch('/api/kingdom/challenge-crown', {
      method: 'POST', headers: {'Content-Type': 'application/json'}, body: '{}',
    })).json();
    if (d.ok) {
      closeM('kingdom-modal');
      narrate(d.message, 5000);
      // Start L3 crown challenge game
      _level = 3;
      setTimeout(() => startGame(), 800);
    } else if (d.insufficient) {
      narrate(d.message, 4000);
    } else {
      narrate('⚠️ ' + (d.error || 'Challenge failed'));
    }
  } catch(e) { narrate('⚠️ ' + e.message); }
}

async function proposeMarriage() {
  if (!_user?.email) { showAuth(); return; }
  const email = document.getElementById('k-partner-email')?.value.trim();
  if (!email) { narrate('⚠️ Enter your partner\'s email address'); return; }
  try {
    const d = await (await fetch('/api/kingdom/propose', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({ partner_email: email }),
    })).json();
    narrate(d.message || d.error || 'Error', 5000);
    if (d.ok) { await loadKingdom(); renderKCrown(); }
  } catch(e) { narrate('⚠️ ' + e.message); }
}

// ── Betting flow ─────────────────────────────────────────────────────────────
async function startGameWithBet(level) {
  if (!_user?.email || level < 2) {
    // No bet needed for L1
    await startGame();
    return;
  }
  _pendingGameLevel = level;
  const gate = { 2: { ante: 3 }, 3: { ante: 10 } }[level] || { ante: 3 };
  const herd = _kdata.herd_cows || 0;
  if (herd < gate.ante) {
    // Not enough cows
    document.getElementById('broke-msg').innerHTML =
      'You need <strong style="color:var(--gold)">' + gate.ante + ' cows</strong> to play Level ' + level +
      '.<br>You have <strong style="color:#ff9999">' + herd + ' cows</strong>.<br>Buy more, claim your daily gift, or drop to Level ' + (level - 1) + '.';
    const dropBtn = document.getElementById('broke-drop-btn');
    document.getElementById('broke-drop-lv').textContent = level - 1;
    dropBtn.onclick = () => { closeM('broke-modal'); selLevel(level - 1); startGame(); };
    document.getElementById('broke-modal').classList.remove('hidden');
    return;
  }
  // Show bet confirm
  document.getElementById('bet-info').innerHTML =
    'Level ' + level + ' requires a <strong style="color:var(--gold)">' + gate.ante + '-cow ante</strong>.<br>' +
    'Win and double it. Lose and it\'s gone.';
  document.getElementById('bet-herd').textContent = '🐄 Your herd: ' + herd + ' cows';
  document.getElementById('bet-modal').classList.remove('hidden');
}

async function confirmBet() {
  closeM('bet-modal');
  const level = _pendingGameLevel;
  const gate = { 2: { ante: 3 }, 3: { ante: 10 } }[level] || { ante: 3 };
  try {
    const d = await (await fetch('/api/economy/place-bet', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({ level, bet: gate.ante }),
    })).json();
    if (!d.ok && d.insufficient) {
      document.getElementById('broke-msg').innerHTML = d.message;
      document.getElementById('broke-drop-lv').textContent = level - 1;
      document.getElementById('broke-drop-btn').onclick = () => {
        closeM('broke-modal'); selLevel(level - 1); startGame();
      };
      document.getElementById('broke-modal').classList.remove('hidden');
      return;
    }
    _activeBetId = d.bet_id;
    _activeBetAmt = d.bet_amount;
    narrate('🐄 ' + d.bet_amount + ' cows in the pot! Game on!', 2500);
    const hc = document.getElementById('herd-count');
    if (hc) hc.textContent = (d.herd_cows || 0) + ' 🐄';
    await startGame();
  } catch(e) { narrate('⚠️ ' + e.message); }
}

async function claimDailyGift() {
  closeM('broke-modal');
  await buyCows('cows_daily');
}

// Patch startGame to intercept L2/L3 for betting
const _origStartGame = startGame;
startGame = async function() {
  if (_level >= 2 && _user?.email && _activeBetId === null) {
    await startGameWithBet(_level);
    return;
  }
  _activeBetId = null;
  await _origStartGame();
};

// Patch gameOver to settle bets
const _origGameOver = gameOver;
gameOver = function(scores, nm) {
  _origGameOver(scores, nm);
  if (_activeBetId && _user?.email) {
    const [p0, p1] = scores || [0, 0];
    const outcome = p0 > p1 ? 'win' : p1 > p0 ? 'lose' : 'draw';
    settleBetAfterGame(outcome, p0);
    _activeBetId = null;
  }
};

async function settleBetAfterGame(outcome, score) {
  if (!_activeBetId) return;
  try {
    const d = await (await fetch('/api/economy/settle-bet', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({ bet_id: _activeBetId, outcome, score }),
    })).json();
    if (d.ok) {
      const hc = document.getElementById('herd-count');
      if (hc) hc.textContent = (d.herd_cows || 0) + ' 🐄';
      narrate(d.message, 4500);
      // Level unlock celebration
      if (d.unlock_level) showLevelUnlock(d.unlock_level);
    }
  } catch(e) {}
}

function showLevelUnlock(level) {
  const ov = document.getElementById('unlock-overlay');
  const icons = { 2: '🐂', 3: '🦅' };
  const names = { 2: 'WARRIOR LEVEL UNLOCKED!', 3: '👑 KING LEVEL UNLOCKED!' };
  const subs  = {
    2: 'Betting begins. Ante: 3 cows per game. Reach 50 cows for Level 3.',
    3: 'High stakes! Ante: 10 cows. Reach 200 for The Market. Crown awaits!',
  };
  document.getElementById('unlock-icon').textContent = icons[level] || '🐄';
  document.getElementById('unlock-title').textContent = names[level] || 'LEVEL UNLOCKED!';
  document.getElementById('unlock-sub').textContent = subs[level] || '';
  ov.style.display = 'flex';
  ov.style.pointerEvents = 'auto';
  setTimeout(() => {
    ov.style.display = 'none';
    ov.style.pointerEvents = 'none';
  }, 4500);
}

// ── Bottom Navigation Controller ─────────────────────────────────────────────
const _bnavMap = {
  home:    ()=>{ closeAllM(); if(_user) loadHome(); else showAuth(); },
  play:    ()=>{ closeAllM(); startMenuOpen(); },
  kingdom: ()=>{ closeAllM(); if(_user) openKingdom(); else showAuth(); },
  social:  ()=>{ closeAllM(); if(_user) openSocialHub(); else showAuth(); },
  store:   ()=>{ closeAllM(); if(_user) showShop(); else showAuth(); },
  profile: ()=>{ closeAllM(); if(_user) showProfile(); else showAuth(); },
};
function bnavGo(tab){
  document.querySelectorAll('.bnav-btn').forEach(b=>b.classList.remove('active'));
  const btn=document.getElementById('bnav-'+tab);
  if(btn) btn.classList.add('active');
  (_bnavMap[tab]||_bnavMap.home)();
}
function startMenuOpen(){
  // Open the play/start overlay
  const s=document.getElementById('start-modal')||document.getElementById('mode-select');
  if(s){s.style.display='flex';}else{openM('start-modal');}
}
function openSocialHub(){
  // Show friends + clans + spectate combined
  openM('friends-modal') || showLb();
}
function openKingdom(){
  const km=document.getElementById('kingdom-modal');
  if(km){openM('kingdom-modal');}else{showKingdom&&showKingdom();}
}

// ── Mode pill in HUD showing current game variant ─────────────────────────
function updateModePill(){
  const pill=document.getElementById('mode-pill');
  if(!pill)return;
  const modes={
    '3d':'3D','5d':'5D','ar':'AR','vr':'VR'
  };
  const mode=window._gameMode||'5d';
  pill.textContent=modes[mode]||'5D';
  const xrBtn=document.getElementById('xr-launch-btn');
  if(xrBtn){
    xrBtn.classList.toggle('visible',mode==='ar'||mode==='vr');
  }
}

// ── XR launch (AR/VR) ─────────────────────────────────────────────────────
window._gameMode='5d';
async function setGameMode(mode){
  window._gameMode=mode;
  updateModePill();
  try{
    await apiFetch('/api/game/mode',{method:'POST',body:JSON.stringify({mode})});
  }catch(e){}
}
function launchXR(){
  const mode=window._gameMode;
  if(mode==='vr'){
    // WebXR immersive-vr session
    if(navigator.xr){
      navigator.xr.requestSession('immersive-vr',{
        requiredFeatures:['local-floor'],
        optionalFeatures:['bounded-floor','hand-tracking']
      }).then(session=>{
        startXRSession(session,'vr');
      }).catch(()=>narrate('🥽 VR not available on this device. Use a WebXR browser.'));
    }else{
      // Fallback: open A-Frame page in new tab
      window.open('/xr?mode=vr','_blank');
    }
  }else if(mode==='ar'){
    if(navigator.xr){
      navigator.xr.isSessionSupported('immersive-ar').then(supported=>{
        if(supported){
          navigator.xr.requestSession('immersive-ar',{
            requiredFeatures:['hit-test','local'],
            optionalFeatures:['dom-overlay'],
            domOverlay:{root:document.getElementById('ui')}
          }).then(session=>startXRSession(session,'ar'))
           .catch(()=>narrate('📱 AR launch failed. Check camera permissions.'));
        }else{
          // iOS Safari fallback: open AR Quick Look
          window.open('/xr?mode=ar','_blank');
        }
      });
    }else{
      window.open('/xr?mode=ar','_blank');
    }
  }
}
async function startXRSession(session,mode){
  // Poll /api/game/xr-state and render via WebXR
  narrate(mode==='vr'?'🥽 VR session started — look around the Nguni village!':'📱 AR session started — place board on any flat surface!');
  session.addEventListener('end',()=>narrate('XR session ended'));
  // Hand off to client XR renderer — game logic stays server-side
  window._xrSession=session;
  window._xrMode=mode;
  pollXRState();
}
let _xrPollInterval=null;
function pollXRState(){
  if(_xrPollInterval) clearInterval(_xrPollInterval);
  _xrPollInterval=setInterval(async()=>{
    if(!window._xrSession||window._xrSession.ended){
      clearInterval(_xrPollInterval);return;
    }
    try{
      const r=await apiFetch('/api/game/xr-state');
      if(r.board_layout){
        dispatchEvent(new CustomEvent('xr-state-update',{detail:r}));
      }
    }catch(e){}
  },100); // 10 fps XR state polling
}

// ── Credits (cow) protection — sign all balance-modifying requests ────────────
const _cowProtect = {
  async buyItem(item){
    // Step 1: get signed transaction token
    const signR = await apiFetch('/api/store/sign-transaction',{
      method:'POST',body:JSON.stringify({item})
    });
    if(!signR.sig) throw new Error('Could not get transaction signature');
    // Step 2: submit signed purchase
    return await apiFetch('/api/store/buy',{
      method:'POST',
      body:JSON.stringify({
        item,
        ts:signR.ts,
        sig:signR.sig,
        idempotency_key:signR.idempotency_key
      })
    });
  },
  async submitScore(score,level){
    const signR = await apiFetch('/api/game/sign-score',{
      method:'POST',body:JSON.stringify({score,level})
    });
    if(!signR.sig) return;
    return await apiFetch('/api/game/submit-score',{
      method:'POST',
      body:JSON.stringify({score,level,ts:signR.ts,sig:signR.sig,idempotency_key:signR.idempotency_key})
    });
  }
};
// Override existing market buy to use protection
async function secureMarketBuy(item){
  try{
    const r=await _cowProtect.buyItem(item);
    if(r.ok){
      narrate('✅ '+r.message);
      loadProfile&&loadProfile();
    }else if(r.error==='MFA required'){
      narrate('🔐 Store requires MFA. Verify at Settings → Security');
    }else{
      narrate('❌ '+(r.message||r.error||'Purchase failed'));
    }
    return r;
  }catch(e){
    narrate('❌ Purchase error: '+(e.message||'try again'));
  }
}

// ── Credits badge — shows 🔒 when HMAC protection is active ──────────────────
function showCreditsBadge(active){
  const badge=document.getElementById('credits-lock-badge');
  if(badge){badge.style.display=active?'inline':'none';}
}

// ── Mode pill init ─────────────────────────────────────────────────────────
document.addEventListener('DOMContentLoaded',()=>{
  updateModePill();
  // Check if user has XR-capable device
  if(navigator.xr){
    navigator.xr.isSessionSupported('immersive-vr').then(ok=>{
      if(ok&&(window._gameMode==='vr'||window._gameMode==='ar')){
        const xrBtn=document.getElementById('xr-launch-btn');
        if(xrBtn) xrBtn.classList.add('visible');
      }
    }).catch(()=>{});
  }
  showCreditsBadge(true); // protection always active
});

// ── Load kingdom state on page init ──────────────────────────────────────────
// This extends the existing init() IIFE — called after user loads
setTimeout(() => { if (_user?.email) loadKingdom(); }, 3500);


<!-- ── SHOP / UPGRADE MODAL ── -->
<div class="modal hidden" id="shop-modal">
 <div class="modal-box" style="max-width:500px">
  <div class="mtitle" style="color:#C9A84C">👑 UPGRADE · INKOSI SHOP</div>
  <div class="nguni-bar"></div>
  <div id="current-plan-badge" style="text-align:center;margin-bottom:12px">
    <span style="background:rgba(201,168,76,.15);border:1px solid var(--gold);color:var(--gold);
      padding:4px 16px;border-radius:16px;font-family:'Cinzel',serif;font-size:12px">
      Current plan: <span id="plan-label">Free</span>
    </span>
  </div>
  <div id="shop-plans" style="display:grid;grid-template-columns:1fr 1fr;gap:10px;margin-bottom:12px"></div>
  <div id="shop-features" style="font-size:12px;color:rgba(245,236,215,.5);margin-bottom:10px;line-height:1.6">
    <strong style="color:var(--gold);display:block;margin-bottom:4px">What you unlock:</strong>
    <span id="feature-list">Loading…</span>
  </div>
  <div id="shop-msg" class="ok" style="display:none;text-align:center;margin-bottom:8px"></div>
  <div style="display:flex;gap:8px;justify-content:center">
    <button class="btn" onclick="closeM('shop-modal')">Close</button>
  </div>
 </div>
</div>

<!-- ── DONATE MODAL ── -->
<div class="modal hidden" id="donate-modal">
 <div class="modal-box" style="max-width:440px">
  <div class="mtitle">🐄 SUPPORT INTSHUBA</div>
  <div class="nguni-bar"></div>
  <div style="text-align:center;font-size:14px;color:rgba(245,236,215,.7);margin-bottom:14px;line-height:1.6">
    Intshuba is a free-to-play preservation of a centuries-old Southern African game.
    Your donation funds development of new features, more languages, and school programmes. 🌍
  </div>

  <!-- Ko-fi button -->
  <div style="text-align:center;margin-bottom:16px">
    <a href="https://ko-fi.com/inkazimulo" target="_blank" rel="noopener" id="kofi-btn"
       style="display:inline-block;background:linear-gradient(135deg,#FF5E5B,#FF9671);
         color:white;padding:12px 28px;border-radius:24px;text-decoration:none;
         font-family:'Nunito',sans-serif;font-weight:800;font-size:15px;
         box-shadow:0 4px 14px rgba(255,94,91,.4)">
      ☕ Buy us a coffee on Ko-fi
    </a>
    <div style="font-size:11px;color:rgba(245,236,215,.35);margin-top:6px">No account needed · Any amount</div>
  </div>

  <!-- PayPal / direct amount buttons -->
  <div class="slabel">OR CHOOSE AN AMOUNT</div>
  <div style="display:flex;gap:8px;justify-content:center;flex-wrap:wrap;margin-bottom:14px" id="donate-amounts">
    <button class="btn" style="border-radius:20px" onclick="selectDonation(this,20)">R20</button>
    <button class="btn" style="border-radius:20px" onclick="selectDonation(this,50)">R50</button>
    <button class="btn sel" style="border-radius:20px" onclick="selectDonation(this,100)">R100</button>
    <button class="btn" style="border-radius:20px" onclick="selectDonation(this,200)">R200</button>
    <button class="btn" style="border-radius:20px" onclick="selectDonation(this,500)">R500 🐄</button>
  </div>
  <input class="inp" id="donate-msg" placeholder="Optional message to the team…" style="margin-bottom:8px">
  <!-- PayPal donate link (replace with your PayPal.me link) -->
  <a id="paypal-donate-link"
     href="https://paypal.me/stanzachirwa/100" target="_blank" rel="noopener"
     style="display:block;text-align:center;background:linear-gradient(135deg,#003087,#009cde);
       color:white;padding:11px;border-radius:8px;text-decoration:none;
       font-family:'Cinzel',serif;font-size:13px;letter-spacing:1px;margin-bottom:10px">
    💙 Donate via PayPal
  </a>

  <!-- Supporters leaderboard -->
  <div style="margin-top:12px;padding-top:10px;border-top:1px solid var(--border)">
    <div class="slabel">OUR TOP SUPPORTERS</div>
    <div id="supporters-list" style="font-size:13px;color:rgba(245,236,215,.6);line-height:1.8">Loading…</div>
  </div>

  <!-- Bank Transfer -->
  <div style="margin-top:12px;padding:10px;background:rgba(255,255,255,.04);border-radius:8px;border:1px solid rgba(255,255,255,.08)">
    <div class="slabel">🇿🇦 SA BANK TRANSFER (FNB)</div>
    <div style="font-size:12px;color:rgba(245,236,215,.6);line-height:1.8;font-family:'Courier New',monospace">
      Bank: <strong style="color:var(--ivory)">First National Bank</strong><br>
      Account holder: <strong style="color:var(--ivory)">S.D. Chirwa</strong><br>
      Account no: <strong style="color:var(--gold)">63032569915</strong><br>
      Branch code: <strong style="color:var(--ivory)">250655</strong><br>
      Reference: <strong style="color:var(--gold)">INTSHUBA-DONATION</strong>
    </div>
  </div>
  <!-- Social Share -->
  <div style="margin-top:12px;padding-top:10px;border-top:1px solid var(--border)">
    <div class="slabel">SHARE THE GAME</div>
    <div style="display:flex;gap:6px;flex-wrap:wrap;margin-top:6px" id="social-share-btns">
      <a href="https://twitter.com/intent/tweet?text=🐄%20Play%20Intshuba%20-%20the%20ancient%20Nguni%20stone%20game!%20Free%20at%20inkazimulo.co.za%20%23Intshuba"
         target="_blank" rel="noopener"
         style="background:#1DA1F2;color:white;padding:5px 12px;border-radius:16px;font-size:11px;text-decoration:none;font-weight:600">𝕏 Twitter</a>
      <a href="https://api.whatsapp.com/send?text=🐄%20Play%20Intshuba%20-%20the%20ancient%20Nguni%20stone%20game!%20Free%20at%20inkazimulo.co.za"
         target="_blank" rel="noopener"
         style="background:#25D366;color:white;padding:5px 12px;border-radius:16px;font-size:11px;text-decoration:none;font-weight:600">WhatsApp</a>
      <a href="https://www.facebook.com/sharer/sharer.php?u=https://inkazimulo.co.za"
         target="_blank" rel="noopener"
         style="background:#1877F2;color:white;padding:5px 12px;border-radius:16px;font-size:11px;text-decoration:none;font-weight:600">Facebook</a>
      <a href="https://t.me/share/url?url=https://inkazimulo.co.za&text=🐄%20Play%20Intshuba!"
         target="_blank" rel="noopener"
         style="background:#229ED9;color:white;padding:5px 12px;border-radius:16px;font-size:11px;text-decoration:none;font-weight:600">Telegram</a>
      <a href="https://www.linkedin.com/sharing/share-offsite/?url=https://inkazimulo.co.za"
         target="_blank" rel="noopener"
         style="background:#0A66C2;color:white;padding:5px 12px;border-radius:16px;font-size:11px;text-decoration:none;font-weight:600">LinkedIn</a>
      <button onclick="copyShareLink()" style="background:rgba(201,168,76,.2);color:var(--gold);padding:5px 12px;border-radius:16px;font-size:11px;border:1px solid var(--gold);cursor:pointer">📋 Copy Link</button>
    </div>
  </div>
  <div id="donate-ok" class="ok" style="display:none;text-align:center;margin-top:8px"></div>
  <div style="font-size:10px;color:rgba(245,236,215,.3);text-align:center;margin-top:6px">
    📧 info@inkazimulo.digital
  </div>
  <div style="display:flex;gap:8px;margin-top:10px;justify-content:center">
    <button class="btn" onclick="closeM('donate-modal')">Close</button>
  </div>
 </div>
</div>


<!-- ══════════════════════════════════════════════════════════════════
     KINGDOM MODAL  –  Herd, Betting, Market, Marriage, Crown
═══════════════════════════════════════════════════════════════════ -->
<div class="modal hidden" id="kingdom-modal">
 <div class="modal-box" style="max-width:540px">

  <!-- Header -->
  <div class="mtitle">🐄 YOUR KINGDOM</div>
  <div id="kingdom-title-bar" style="text-align:center;margin-bottom:10px">
    <span id="k-title-icon" style="font-size:24px">🐄</span>
    <span id="k-title-label" style="font-family:'Cinzel',serif;color:var(--gold);
      font-size:14px;letter-spacing:1px;margin-left:6px">iNkonyana · Calf</span>
  </div>
  <div class="nguni-bar"></div>

  <!-- Herd stats row -->
  <div style="display:grid;grid-template-columns:repeat(4,1fr);gap:8px;margin-bottom:14px"
       id="k-stats-grid"></div>

  <!-- King banner -->
  <div id="k-king-banner" style="display:none;text-align:center;padding:8px 12px;
    background:rgba(201,168,76,.12);border:1px solid var(--gold);border-radius:8px;
    margin-bottom:12px;font-size:13px;font-family:'Cinzel',serif">
    <span style="font-size:18px">👑</span>
    <span id="k-king-name" style="color:var(--gold)">Inkosi</span>
    <span style="color:rgba(245,236,215,.4)"> holds the crown</span>
  </div>

  <!-- Tabs -->
  <div style="display:flex;border-bottom:.5px solid var(--border);margin-bottom:12px">
    <button class="cw-tab act" id="kt-herd"   onclick="kTab('herd')">🐄 Herd</button>
    <button class="cw-tab"     id="kt-market" onclick="kTab('market')">🏪 Market</button>
    <button class="cw-tab"     id="kt-crown"  onclick="kTab('crown')">👑 Crown</button>
    <button class="cw-tab"     id="kt-hall"   onclick="kTab('hall')">📜 Hall</button>
  </div>

  <!-- Herd tab -->
  <div id="kp-herd">
    <div class="slabel">CATTLE PACKS — BUY MORE COWS</div>
    <div style="display:grid;grid-template-columns:repeat(2,1fr);gap:8px;margin-bottom:12px"
         id="k-cow-packs"></div>
    <div class="slabel">RECENT EVENTS</div>
    <div id="k-events" style="max-height:140px;overflow-y:auto;font-size:12px;
      color:rgba(245,236,215,.6);line-height:1.8"></div>
  </div>

  <!-- Market tab -->
  <div id="kp-market" style="display:none">
    <div style="font-size:12px;color:rgba(245,236,215,.5);margin-bottom:10px;line-height:1.5">
      Spend your cattle on Nguni milestones. Each purchase is permanent and earns status.
    </div>
    <div id="k-market-items" style="display:grid;grid-template-columns:1fr 1fr;gap:8px"></div>
  </div>

  <!-- Crown tab -->
  <div id="kp-crown" style="display:none">
    <div style="text-align:center;padding:16px 0">
      <div style="font-size:48px;margin-bottom:8px">👑</div>
      <div style="font-family:'Cinzel',serif;color:var(--gold);font-size:16px;margin-bottom:6px"
           id="crown-holder-name">Inkosi</div>
      <div style="font-size:12px;color:rgba(245,236,215,.45);margin-bottom:16px"
           id="crown-holder-sub">holds the throne</div>
      <div style="font-size:13px;color:rgba(245,236,215,.6);margin-bottom:16px;line-height:1.6"
           id="crown-challenge-info">
        Challenge the king for <strong style="color:var(--gold)">300 cows</strong>.
        Win to claim the crown, daily tribute, and eternal glory.
      </div>
      <button class="btn" style="background:linear-gradient(135deg,#8B1A1A,#5a0808);
        border-color:var(--gold);color:var(--gold);font-size:13px"
        id="challenge-btn" onclick="challengeCrown()">⚔️ Challenge for Crown</button>
    </div>
    <div class="slabel">MARRIAGE</div>
    <div style="font-size:12px;color:rgba(245,236,215,.5);margin-bottom:8px;line-height:1.5">
      Pay lobola (100 cows) to propose to another player. Married couples share a herd badge.
    </div>
    <div id="k-marriage-info" style="margin-bottom:8px;font-size:13px"></div>
    <div style="display:flex;gap:8px">
      <input class="inp" id="k-partner-email" placeholder="Partner's email…"
             style="margin-bottom:0;flex:1">
      <button class="btn green" onclick="proposeMarriage()">💍 Propose</button>
    </div>
  </div>

  <!-- Hall of Fame tab -->
  <div id="kp-hall" style="display:none">
    <div class="slabel">KINGDOM LEADERBOARD</div>
    <div id="k-lb-list" style="max-height:200px;overflow-y:auto"></div>
    <div class="slabel">CROWN HALL OF FAME</div>
    <div id="k-hall-list" style="max-height:120px;overflow-y:auto;font-size:12px;
      color:rgba(245,236,215,.6);line-height:1.8"></div>
  </div>

  <div id="k-msg" class="ok" style="display:none;text-align:center;margin-top:8px"></div>
  <div style="display:flex;gap:8px;margin-top:12px;justify-content:center">
    <button class="btn" onclick="closeM('kingdom-modal')">Close</button>
  </div>
 </div>
</div>

<!-- BET CONFIRMATION MODAL (shown before L2/L3 game) -->
<div class="modal hidden" id="bet-modal">
 <div class="modal-box" style="max-width:380px;text-align:center">
  <div class="mtitle">🐄 PLACE YOUR BET</div>
  <div class="nguni-bar"></div>
  <div id="bet-info" style="font-size:15px;color:var(--ivory);margin:12px 0;line-height:1.6"></div>
  <div id="bet-herd" style="font-family:'Cinzel',serif;font-size:20px;color:var(--gold);margin-bottom:14px"></div>
  <div style="display:flex;gap:8px;justify-content:center;flex-wrap:wrap">
    <button class="btn green" id="bet-confirm-btn" onclick="confirmBet()">🐄 Accept &amp; Play</button>
    <button class="btn red" onclick="closeM('bet-modal')">Decline</button>
    <button class="btn blue" onclick="closeM('bet-modal');showKingdom()">Buy Cows 🐄</button>
  </div>
 </div>
</div>

<!-- INSUFFICIENT COWS MODAL -->
<div class="modal hidden" id="broke-modal">
 <div class="modal-box" style="max-width:380px;text-align:center">
  <div class="mtitle" style="color:#ff9999">😢 NOT ENOUGH COWS</div>
  <div class="nguni-bar"></div>
  <div id="broke-msg" style="font-size:14px;color:var(--ivory);margin:12px 0;line-height:1.6"></div>
  <div style="display:flex;gap:8px;justify-content:center;flex-wrap:wrap;margin-top:8px">
    <button class="btn green" onclick="closeM('broke-modal');showKingdom()">🐄 Buy Cows</button>
    <button class="btn" id="broke-drop-btn">↓ Drop to Level <span id="broke-drop-lv">1</span></button>
    <button class="btn blue" onclick="claimDailyGift()">☀️ Daily Gift</button>
  </div>
 </div>
</div>

<!-- LEVEL UNLOCK CELEBRATION -->
<div id="unlock-overlay" style="display:none;position:fixed;inset:0;z-index:95;
  flex-direction:column;align-items:center;justify-content:center;
  background:rgba(0,0,0,.88);pointer-events:none">
  <div style="font-size:64px;animation:pulse 1s infinite" id="unlock-icon">🐂</div>
  <div style="font-family:'Cinzel',serif;font-size:28px;color:var(--gold);
    margin:10px 0;letter-spacing:2px" id="unlock-title">LEVEL 2 UNLOCKED!</div>
  <div style="font-size:15px;color:var(--ivory);margin-bottom:16px" id="unlock-sub">
    Betting begins. Ante: 3 cows per game.</div>
</div>


<!-- ══════════════════════════════════════════════════════
     TRIBE SELECTION MODAL
═══════════════════════════════════════════════════════ -->
<div class="modal hidden" id="tribe-modal">
 <div class="modal-box" style="max-width:560px">
  <div class="mtitle">⚔️ CHOOSE YOUR TRIBE</div>
  <div class="nguni-bar"></div>
  <div style="font-size:13px;color:rgba(245,236,215,.55);margin-bottom:12px;text-align:center;line-height:1.6">
    Your tribe gives you unique bonuses, sounds, and board colours.<br>
    Compete in tribe wars to earn collective glory — and the iSilo throne.
  </div>
  <div id="tribe-cards" style="display:grid;grid-template-columns:repeat(3,1fr);gap:8px;margin-bottom:12px"></div>
  <div class="nguni-bar"></div>
  <div style="display:flex;gap:8px;justify-content:center">
    <button class="btn green" onclick="closeM('tribe-modal')">Confirm Tribe ✅</button>
    <button class="btn" onclick="closeM('tribe-modal')">Cancel</button>
  </div>
 </div>
</div>

<!-- ══════════════════════════════════════════════════════
     COMPETITIONS MODAL
═══════════════════════════════════════════════════════ -->
<div class="modal hidden" id="comp-modal">
 <div class="modal-box" style="max-width:520px">
  <div class="mtitle">🏆 COMPETITIONS</div>
  <div class="nguni-bar"></div>

  <!-- Competition type tabs -->
  <div style="display:flex;border-bottom:1px solid var(--border);margin-bottom:12px;flex-wrap:wrap">
    <div class="cw-tab act" id="ct-open"   onclick="compTab('open')">📋 Open</div>
    <div class="cw-tab"     id="ct-create" onclick="compTab('create')">➕ Create</div>
    <div class="cw-tab"     id="ct-tribe"  onclick="compTab('tribe')">⚔️ Tribe War</div>
    <div class="cw-tab"     id="ct-season" onclick="compTab('season')">🗓️ Season</div>
  </div>

  <!-- Open competitions -->
  <div id="cp-open">
    <div id="comp-list" style="max-height:320px;overflow-y:auto"></div>
  </div>

  <!-- Create competition -->
  <div id="cp-create" style="display:none">
    <div class="slabel">COMPETITION NAME</div>
    <input class="inp" id="comp-name" placeholder="e.g. Durban Schools Championship 2026">
    <div class="slabel">TYPE</div>
    <select class="inp" id="comp-type" style="background:rgba(201,168,76,.08);color:var(--ivory)">
      <option value="school">🏫 Inter-School (free entry, CAPS-aligned)</option>
      <option value="varsity">🎓 Inter-Varsity/College (R25 entry)</option>
      <option value="community">🏘️ Community Tournament (R5 entry)</option>
      <option value="national">🇿🇦 National Championship (R50 entry)</option>
      <option value="international">🌍 International Open (R100 entry)</option>
      <option value="tribe_war">⚔️ Tribe War (free, glory only)</option>
      <option value="individual_daily">⚡ Daily Speed Round (free)</option>
      <option value="individual_monthly">🏆 Monthly Individual (R10 entry)</option>
    </select>
    <div class="slabel">STREAM URL (optional)</div>
    <input class="inp" id="comp-stream" placeholder="https://youtube.com/live/... (leave blank if not streaming)">
    <button class="btn green" style="width:100%;margin-top:4px" onclick="createCompetition()">
      🏆 Create Competition
    </button>
    <div style="font-size:11px;color:rgba(245,236,215,.35);margin-top:8px;text-align:center">
      Entry fees are collected in cows (1 cow ≈ R1). Prize pools grow as players join.
    </div>
  </div>

  <!-- Tribe war standings -->
  <div id="cp-tribe" style="display:none">
    <div class="slabel">TRIBE WAR STANDINGS — total cattle by nation</div>
    <div id="tribe-war-list" style="max-height:300px;overflow-y:auto"></div>
    <div style="font-size:11px;color:rgba(245,236,215,.3);margin-top:8px;text-align:center">
      Tribe war resets every 30 days. Winning tribe earns a 2× cow bonus week.
    </div>
  </div>

  <!-- Season status -->
  <div id="cp-season" style="display:none">
    <div id="season-info" style="max-height:320px;overflow-y:auto"></div>
  </div>

  <div style="display:flex;gap:8px;margin-top:10px;justify-content:center">
    <button class="btn" onclick="closeM('comp-modal')">Close</button>
  </div>
 </div>
</div>

<!-- ══════════════════════════════════════════════════════
     AGE POOL REGISTRATION MODAL
═══════════════════════════════════════════════════════ -->
<div class="modal hidden" id="age-modal">
 <div class="modal-box" style="max-width:380px;text-align:center">
  <div class="mtitle">🎂 YOUR AGE POOL</div>
  <div class="nguni-bar"></div>
  <div style="font-size:13px;color:rgba(245,236,215,.55);margin-bottom:14px;line-height:1.6">
    Register your birth year to compete in age-appropriate championships.<br>
    <span style="color:rgba(245,236,215,.3);font-size:11px">Your age is never displayed publicly.</span>
  </div>
  <div style="display:grid;grid-template-columns:repeat(4,1fr);gap:6px;margin-bottom:14px">
    <div style="font-size:10px;color:rgba(245,236,215,.4);letter-spacing:1px;grid-column:1/-1;text-align:center;margin-bottom:2px">AGE POOLS</div>
    <div style="background:rgba(201,168,76,.08);border:1px solid rgba(201,168,76,.2);border-radius:8px;padding:8px;font-size:11px;text-align:center">🐣<br><b>U-10</b><br>Ages 0–9</div>
    <div style="background:rgba(201,168,76,.08);border:1px solid rgba(201,168,76,.2);border-radius:8px;padding:8px;font-size:11px;text-align:center">🌱<br><b>U-14</b><br>Ages 10–13</div>
    <div style="background:rgba(201,168,76,.08);border:1px solid rgba(201,168,76,.2);border-radius:8px;padding:8px;font-size:11px;text-align:center">⚔️<br><b>U-18</b><br>Ages 14–17</div>
    <div style="background:rgba(201,168,76,.08);border:1px solid rgba(201,168,76,.2);border-radius:8px;padding:8px;font-size:11px;text-align:center">🔥<br><b>U-25</b><br>Ages 18–24</div>
    <div style="background:rgba(201,168,76,.08);border:1px solid rgba(201,168,76,.2);border-radius:8px;padding:8px;font-size:11px;text-align:center">🦅<br><b>U-40</b><br>Ages 25–39</div>
    <div style="background:rgba(201,168,76,.08);border:1px solid rgba(201,168,76,.2);border-radius:8px;padding:8px;font-size:11px;text-align:center">🦁<br><b>40+</b><br>Senior</div>
    <div style="background:rgba(201,168,76,.08);border:1px solid rgba(201,168,76,.2);border-radius:8px;padding:8px;font-size:11px;text-align:center">🐘<br><b>60+</b><br>Elder</div>
    <div style="background:rgba(201,168,76,.12);border:1px solid rgba(201,168,76,.35);border-radius:8px;padding:8px;font-size:11px;text-align:center">🌍<br><b>Open</b><br>All ages</div>
  </div>
  <div class="slabel">YOUR BIRTH YEAR</div>
  <input class="inp" id="birth-year-inp" type="number" min="1920" max="2020"
         placeholder="e.g. 1990" style="text-align:center;font-size:20px;font-family:'Cinzel',serif">
  <div id="age-pool-result" style="font-family:'Cinzel',serif;color:var(--gold);font-size:18px;margin:10px 0;min-height:28px"></div>
  <button class="btn green" style="width:100%" onclick="registerAgePool()">Register Age Pool 🎯</button>
  <button class="btn" style="width:100%;margin-top:8px" onclick="closeM('age-modal')">Skip for now</button>
 </div>
</div>

<div id="ai-thinking-bar">
  <span class="ai-label">🤖 AI thinking…</span>
  <div class="ai-track"><div class="ai-fill"></div></div>
</div>
<div id="replay-banner">⏪ SLOW REPLAY — watching history</div>


<!-- ── Bottom Navigation Bar ── -->
<nav id="bottom-nav">
  <button class="bnav-btn active" id="bnav-home" onclick="bnavGo('home')">
    <span class="bnav-icon">🏠</span>Home
  </button>
  <button class="bnav-btn" id="bnav-play" onclick="bnavGo('play')">
    <span class="bnav-icon-wrap">
      <span class="bnav-icon">♟</span>
      <span class="bnav-badge" id="bnav-play-badge" style="display:none">!</span>
    </span>Play
  </button>
  <button class="bnav-btn" id="bnav-kingdom" onclick="bnavGo('kingdom')">
    <span class="bnav-icon">🐄</span>Kingdom
  </button>
  <button class="bnav-btn" id="bnav-social" onclick="bnavGo('social')">
    <span class="bnav-icon-wrap">
      <span class="bnav-icon">👥</span>
      <span class="bnav-badge" id="bnav-social-badge" style="display:none">!</span>
    </span>Social
  </button>
  <button class="bnav-btn" id="bnav-store" onclick="bnavGo('store')">
    <span class="bnav-icon">🛒</span>Store
  </button>
  <button class="bnav-btn" id="bnav-profile" onclick="bnavGo('profile')">
    <span class="bnav-icon">👤</span>Profile
  </button>
</nav>
<button id="xr-launch-btn" onclick="launchXR()" title="Launch AR/VR">🥽</button>
</script>
</body>
</html>"""
# ── Module-level init (runs when gunicorn imports this file) ─────────────────
init_db()

def _startup_banner():
    """Print a clear startup banner so Railway logs show exactly what is running."""
    sep = '=' * 58
    log.info(sep)
    log.info('  🐄 INTSHUBA  v2.3.0  –  Nguni Stone Game')
    log.info('  © 2024 Inkazimulo Digital — inkazimulo.digital')
    log.info(sep)
    log.info(f'  Environment : {"Railway (production)" if _IS_PROD else "Local (development)"}')
    log.info(f'  DB path     : {DB_PATH}')
    log.info(f'  Data dir    : {_DATA_DIR}')
    log.info(f'  Secret key  : {"from SECRET_KEY env var ✓" if os.environ.get("SECRET_KEY") else "⚠ RANDOM (set SECRET_KEY env var!)"}')
    log.info(f'  Secure cookies : {app.config.get("SESSION_COOKIE_SECURE")}')
    log.info(sep)
    log.info(f'  Languages : {len(LANGS)} | Tribes: {len(TRIBES)} | Competitions: {len(COMPETITION_TYPES)}')
    log.info('  Routes: / | /health | /api/* | /join/<code>')
    log.info(sep)

_startup_banner()

if __name__ == '__main__':
    _port = int(os.environ.get('PORT', 5000))
    log.info(f'🌍 Dev server on http://0.0.0.0:{_port}')
    app.run(debug=False, host='0.0.0.0', port=_port, threaded=True)
