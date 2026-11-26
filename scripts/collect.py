#!/usr/bin/env python3
"""Robot de collecte Exolution : marchés publics (BOAMP), permis de construire
(Sitadel), entreprises et dirigeants (API Recherche d'entreprises), maires (RNE).

Produit les fichiers JSON lus par le site (site/data/). Chaque source est
indépendante : si l'une échoue, les autres sont quand même publiées et l'erreur
est notée dans meta.json.
"""
import csv
import datetime as dt
import gzip
import io
import json
import math
import os
import re
import sys
import time
import traceback
import unicodedata
import zipfile

import requests

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "site", "data")
CACHE = os.path.join(ROOT, "cache")
WORK = os.path.join(ROOT, "work")
for d in (OUT, CACHE, WORK):
    os.makedirs(d, exist_ok=True)

CFG = json.load(open(os.path.join(ROOT, "config.json"), encoding="utf-8"))
TODAY = dt.date.today()
S = requests.Session()
S.headers["User-Agent"] = "exolution-prospection/1.0 (veille open data)"
META = {"genere_le": dt.datetime.now(dt.timezone.utc).isoformat().replace("+00:00", "Z"), "sources": {}, "erreurs": []}

csv.field_size_limit(sys.maxsize)


def log(*a):
    print(*a, flush=True)


def get(url, params=None, tries=4, stream=False, timeout=120):
    last = None
    for i in range(tries):
        try:
            r = S.get(url, params=params, timeout=timeout, stream=stream)
            if r.status_code == 429:
                time.sleep(2 + 3 * i)
                continue
            return r
        except requests.RequestException as e:
            last = e
            time.sleep(2 + 3 * i)
    raise RuntimeError(f"Échec réseau {url}: {last}")


def norm(s):
    s = unicodedata.normalize("NFKD", str(s or "")).encode("ascii", "ignore").decode().lower()
    return re.sub(r"[^a-z0-9]+", " ", s).strip()


def hav(lat1, lon1, lat2, lon2):
    if None in (lat1, lon1, lat2, lon2):
        return None
    p = math.pi / 180
    a = (math.sin((lat2 - lat1) * p / 2) ** 2
         + math.cos(lat1 * p) * math.cos(lat2 * p) * math.sin((lon2 - lon1) * p / 2) ** 2)
    return round(12742 * math.asin(math.sqrt(a)), 1)


BASE = CFG["base"]
Z = CFG["regles_zone"]


def dist(lat, lon):
    return hav(BASE["lat"], BASE["lon"], lat, lon)


def dans_zone(distance, lat, montant, economie_seule=False):
    """Applique les règles de zone d'Exolution. Renvoie (bool, raison)."""
    if economie_seule and Z["economie_france_entiere"]:
        return True, "Économie : France entière"
    if distance is None:
        return False, "lieu inconnu"
    if montant is None:
        ok = distance <= Z["montant_inconnu_rayon_km"]
        return ok, f"montant inconnu, ≤ {Z['montant_inconnu_rayon_km']} km"
    if montant < Z["petit_projet_max_eur"]:
        return distance <= Z["petit_projet_rayon_km"], f"< 500 k€ : ≤ {Z['petit_projet_rayon_km']} km"
    if montant <= Z["moyen_projet_max_eur"]:
        return distance <= Z["moyen_projet_rayon_km"], f"≤ 4 M€ : ≤ {Z['moyen_projet_rayon_km']} km"
    ok = lat is not None and 41 <= lat <= Z["grand_projet_latitude_max"] and distance <= 1000
    return ok, "> 4 M€ : moitié sud, au cas par cas"


def save(name, data):
    with open(os.path.join(OUT, name), "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, separators=(",", ":"))
    log(f"  -> {name} ({len(data) if hasattr(data, '__len__') else ''})")


def step(name):
    def deco(fn):
        def run(*a, **k):
            log(f"\n=== {name} ===")
            t = time.time()
            try:
                res = fn(*a, **k)
                META["sources"][name] = {"ok": True, "duree_s": round(time.time() - t)}
                return res
            except Exception as e:
                traceback.print_exc()
                META["sources"][name] = {"ok": False, "erreur": str(e)[:300]}
                META["erreurs"].append(f"{name}: {str(e)[:300]}")
                return None
        return run
    return deco


# ---------------------------------------------------------------- communes
COMMUNES = {}      # code insee -> {nom, dep, lat, lon}
CP2COM = {}        # code postal -> [codes insee]
NOM2COM = {}       # (dep, nom normalisé) -> code insee
DEP_CENTRE = {}


@step("Communes (geo.api.gouv.fr)")
def load_communes():
    r = get("https://geo.api.gouv.fr/communes", params={
        "fields": "nom,code,codeDepartement,centre,codesPostaux,population",
        "type": "commune-actuelle,arrondissement-municipal", "format": "json"})
    r.raise_for_status()
    acc = {}
    for c in r.json():
        ce = (c.get("centre") or {}).get("coordinates") or [None, None]
        COMMUNES[c["code"]] = {"nom": c["nom"], "dep": c.get("codeDepartement"), "lat": ce[1], "lon": ce[0]}
        for cp in c.get("codesPostaux") or []:
            CP2COM.setdefault(cp, []).append(c["code"])
        NOM2COM[(c.get("codeDepartement"), norm(c["nom"]))] = c["code"]
        if ce[1] is not None:
            a = acc.setdefault(c.get("codeDepartement"), [0, 0, 0])
            a[0] += ce[1]; a[1] += ce[0]; a[2] += 1
    for d, (la, lo, n) in acc.items():
        DEP_CENTRE[d] = (la / n, lo / n)
    log(f"  {len(COMMUNES)} communes")


def commune_info(code):
    return COMMUNES.get(str(code).zfill(5)) if code else None


# ---------------------------------------------------------------- entreprises
ENT_CACHE_F = os.path.join(CACHE, "entreprises.json")
ENT = json.load(open(ENT_CACHE_F, encoding="utf-8")) if os.path.exists(ENT_CACHE_F) else {}
ENT_BUDGET = [CFG["max_enrichissements_par_run"]]


def ffloat(v):
    try:
        return float(v)
    except (TypeError, ValueError):
        return None


def ent_from_result(x):
    siege = x.get("siege") or {}
    dir_ = []
    for d in x.get("dirigeants") or []:
        if d.get("type_dirigeant") == "personne morale" or d.get("denomination"):
            dir_.append({"nom": d.get("denomination") or "", "qualite": d.get("qualite") or "", "morale": True})
        else:
            nom = " ".join(filter(None, [(d.get("prenoms") or "").split(" ")[0].title(), (d.get("nom") or "").upper()]))
            dir_.append({"nom": nom, "qualite": d.get("qualite") or ""})
    return {
        "siren": x.get("siren"),
        "nom": x.get("nom_complet") or x.get("nom_raison_sociale"),
        "naf": x.get("activite_principale"),
        "effectif": x.get("tranche_effectif_salarie"),
        "adresse": siege.get("adresse"),
        "commune": siege.get("libelle_commune"),
        "lat": ffloat(siege.get("latitude")),
        "lon": ffloat(siege.get("longitude")),
        "dirigeants": dir_[:6],
        "actif": x.get("etat_administratif") == "A",
        "maj": TODAY.isoformat(),
    }


def entreprise(siren):
    siren = re.sub(r"\D", "", str(siren or ""))[:9]
    if len(siren) != 9:
        return None
    c = ENT.get(siren)
    if c and c.get("maj", "") >= (TODAY - dt.timedelta(days=45)).isoformat():
        return c
    if ENT_BUDGET[0] <= 0:
        return c
    ENT_BUDGET[0] -= 1
    time.sleep(0.16)
    try:
        r = get("https://recherche-entreprises.api.gouv.fr/search", params={"q": siren, "per_page": 1})
        if r.ok and r.json().get("results"):
            ENT[siren] = ent_from_result(r.json()["results"][0])
        else:
            ENT[siren] = {"siren": siren, "maj": TODAY.isoformat(), "dirigeants": []}
    except Exception as e:
        log("  entreprise", siren, e)
    return ENT.get(siren)


NAME_CACHE_F = os.path.join(CACHE, "noms.json")
NAMES = json.load(open(NAME_CACHE_F, encoding="utf-8")) if os.path.exists(NAME_CACHE_F) else {}


def siren_par_nom(nom, dep=None):
    """Retrouve le SIREN d'un titulaire à partir de son nom (meilleur effort)."""
    key = f"{norm(nom)}|{dep or ''}"
    if key in NAMES:
        return NAMES[key]
    if ENT_BUDGET[0] <= 0:
        return None
    ENT_BUDGET[0] -= 1
    time.sleep(0.16)
    sir = None
    try:
        p = {"q": nom, "per_page": 5}
        if dep:
            p["departement"] = dep
        r = get("https://recherche-entreprises.api.gouv.fr/search", params=p)
        if r.ok:
            n0 = set(norm(nom).split()) - {"sarl", "sas", "sasu", "eurl", "sa", "scp", "selarl", "architectes", "architecte", "et", "associes"}
            for x in r.json().get("results", []):
                n1 = set(norm(x.get("nom_complet")).split())
                if n0 and len(n0 & n1) / len(n0) >= 0.6:
                    sir = x["siren"]
                    if sir not in ENT:
                        ENT[sir] = ent_from_result(x)
                    break
    except Exception as e:
        log("  nom", nom, e)
    NAMES[key] = sir
    return sir


# ---------------------------------------------------------------- maires
MAIRES = {}


@step("Maires (Répertoire national des élus)")
def load_maires():
    r = get("https://www.data.gouv.fr/api/1/datasets/5c34c4d1634f4173183a64f1/")
    r.raise_for_status()
    res = [x for x in r.json().get("resources", []) if "maire" in norm(x.get("title")) and "csv" in (x.get("format") or "").lower()]
    if not res:
        res = [x for x in r.json().get("resources", []) if "maire" in norm(x.get("title") + " " + x.get("url", ""))]
    log("  ressource :", res[0]["title"], res[0]["url"])
    raw = get(res[0]["url"]).content
    txt = raw.decode("utf-8-sig", errors="replace")
    if txt.count("�") > 50:
        txt = raw.decode("latin-1")
    first = txt.splitlines()[0]
    sep = ";" if first.count(";") > first.count(",") else ("\t" if "\t" in first else ",")
    rd = csv.DictReader(io.StringIO(txt), delimiter=sep)
    cols = rd.fieldnames
    log("  colonnes :", cols)
    def col(*keys, excl=()):
        for c in cols:
            n = norm(c)
            if all(k in n for k in keys) and not any(e in n for e in excl):
                return c
    c_code = col("code", "commune") or col("code", "collectivite")
    c_nom = col("nom", "elu") or col("nom", excl=("commune", "naissance", "departement", "collectivite"))
    c_pre = col("prenom")
    c_fonc = col("libelle", "fonction")
    for row in rd:
        code = (row.get(c_code) or "").strip()
        if not code:
            continue
        if c_fonc and row.get(c_fonc) and "maire" not in norm(row[c_fonc]):
            continue
        MAIRES[code.zfill(5)] = f"{(row.get(c_pre) or '').strip().title()} {(row.get(c_nom) or '').strip().upper()}".strip()
    log(f"  {len(MAIRES)} maires")


def maire_de_acheteur(nom, dep):
    m = re.match(r"^\s*(commune|mairie|ville)\s+(de |d'|du |des )?\s*(.+)$", norm(nom).replace(" d ", " d'"))
    if not m:
        return None
    n = norm(m.group(3))
    code = NOM2COM.get((dep, n))
    if code and code in MAIRES:
        return {"nom": MAIRES[code], "qualite": "Maire"}
    return None


# ---------------------------------------------------------------- BOAMP
BOAMP = "https://boamp-datadila.opendatasoft.com/api/explore/v2.1/catalog/datasets/boamp/exports/json"
MOTS = ["maîtrise d'oeuvre", "maîtrise d'œuvre", "maitrise d'oeuvre", "assistance à maîtrise d'ouvrage",
        "ordonnancement", "OPC", "économiste", "économie de la construction", "programmation", "conduite d'opération"]
HORS_BATIMENT = re.compile(r"voirie|assainissement|eau potable|station d.?epuration|reseaux? (d.?eau|humide)|ouvrage d.?art|pont |informatique|logiciel|systeme d.?information|forestier|cours d.?eau|digue|rivi", re.I)


def boamp_query(where, select=None):
    params = {"where": where, "limit": -1}
    if select:
        params["select"] = select
    r = get(BOAMP, params=params, timeout=300)
    if r.status_code == 400 and select:
        log("  select refusé, sans select :", r.text[:300])
        return boamp_query(where)
    if not r.ok:
        raise RuntimeError(f"BOAMP {r.status_code}: {r.text[:300]}")
    return r.json()


def as_list(v):
    if v is None:
        return []
    return v if isinstance(v, list) else [v]


def walk(o, path=""):
    if isinstance(o, dict):
        for k, v in o.items():
            yield from walk(v, f"{path}/{k}")
    elif isinstance(o, list):
        for v in o:
            yield from walk(v, path)
    else:
        yield path, o


def parse_donnees(raw):
    if not raw:
        return None
    if isinstance(raw, (dict, list)):
        return raw
    try:
        return json.loads(raw)
    except Exception:
        return {"texte": str(raw)}


MONTANT_RE = re.compile(
    r"(montant|enveloppe|co[uû]t|budget|estimation)[^0-9€]{0,90}?(\d[\d  .,]*\d)\s*(millions?|M€|M ?euros|k€|K€|€|euros?)", re.I)


def to_eur(num, unit):
    n = num.replace(" ", "").replace(" ", "").replace(" ", "")
    if re.search(r",\d{1,2}$", n):
        n = n.rsplit(",", 1)[0]
    n = n.replace(".", "").replace(",", ".")
    try:
        v = float(n)
    except ValueError:
        return None
    u = unit.lower()
    if u.startswith("m"):
        v *= 1e6
    elif u.startswith("k"):
        v *= 1e3
    return v


DIAG = []


def analyse_avis(rec):
    d = parse_donnees(rec.get("donnees"))
    flat = list(walk(d)) if d else []
    if len(DIAG) < 3 and flat:
        DIAG.append([f"{k} = {str(v)[:50]}" for k, v in flat if isinstance(v, (str, int))][:150])
    texte = " ".join(str(v) for _, v in flat if isinstance(v, str))
    # montant des travaux annoncé dans le texte
    montants = []
    for m in MONTANT_RE.finditer(texte):
        v = to_eur(m.group(2), m.group(3))
        if v and 50_000 <= v <= 500_000_000:
            montants.append(v)
    # code postal / ville (acheteur ou lieu d'exécution)
    cps, villes, contacts, titulaires = [], [], [], []
    for p, v in flat:
        pl = p.lower()
        segs = [x.split(":")[-1] for x in pl.split("/") if x and not x.startswith(("#", "@"))]
        last = segs[-1] if segs else ""
        if not isinstance(v, (str, int)):
            continue
        sv = str(v).strip()
        if last in ("cp", "code_postal", "codepostal", "postalzone", "postal_code", "codepostale") and re.fullmatch(r"\d{5}", sv):
            cps.append(sv)
        if "titulaire" in pl or "winner" in pl or "tenderer" in pl or "contractor" in pl:
            if last in ("denomination", "nom", "officialname", "name", "raison_sociale", "nom_officiel") and len(sv) > 2:
                titulaires.append(sv)
        if ("correspondant" in pl or "contact" in pl) and last in ("nom", "nomcorrespondant", "prenom", "fonction", "tel", "mel", "email", "telephone"):
            contacts.append(sv)
    tit = [t for t in as_list(rec.get("titulaire")) if t] or titulaires
    return {
        "montant": max(montants) if montants else None,
        "cps": cps,
        "titulaires": list(dict.fromkeys(tit))[:6],
        "contact": " · ".join(list(dict.fromkeys(contacts))[:6]) or None,
    }


def missions(txt):
    t = norm(txt)
    m = []
    if re.search(r"\bopc\b|ordonnancement|pilotage", t):
        m.append("OPC")
    if re.search(r"\bdet\b|direction de l.?execution|direction des travaux", t):
        m.append("DET")
    if re.search(r"assistance a maitrise d.?ouvrage|\bamo\b|programmation|programmiste|conduite d.?operation|mandat", t):
        m.append("AMO")
    if re.search(r"economiste|economie de la construction|metre", t):
        m.append("Économie")
    if re.search(r"maitrise d.?oeuvre|\bmoe\b|maitre d.?oeuvre|architecte", t):
        m.append("Maîtrise d'œuvre")
    return m


def type_bat(txt):
    t = norm(txt)
    for k, v in [(r"logement|residence|habitat|ehpad", "Logement collectif"),
                 (r"ecole|college|lycee|gymnase|salle|mairie|equipement|piscine|mediatheque|creche|caserne|hopital|centre", "Équipement public"),
                 (r"bureau|tertiaire|siege", "Tertiaire / bureaux"),
                 (r"commerc|halle|marche couvert", "Commercial"),
                 (r"atelier|industri|usine|entrepot", "Industriel / artisanal")]:
        if re.search(k, t):
            return v
    return "Autre"


def localise(rec, info):
    deps = [str(x) for x in as_list(rec.get("code_departement")) if x]
    for cp in info["cps"]:
        for code in CP2COM.get(cp, []):
            c = COMMUNES.get(code)
            if c and (not deps or c["dep"] in deps):
                return c, False
    if deps and deps[0] in DEP_CENTRE:
        la, lo = DEP_CENTRE[deps[0]]
        return {"nom": f"Département {deps[0]}", "dep": deps[0], "lat": la, "lon": lo}, True
    return None, True


SELECT = ("idweb,objet,nomacheteur,dateparution,datelimitereponse,code_departement,nature,nature_libelle,"
          "type_marche,descripteur_libelle,url_avis,titulaire,donnees,procedure_libelle,famille_libelle")


def fetch_boamp(where_extra, depuis):
    recs = {}
    for mot in MOTS:
        w = f"dateparution >= date'{depuis.isoformat()}' AND \"{mot}\""
        if where_extra:
            w += f" AND ({where_extra})"
        try:
            rows = boamp_query(w, SELECT)
        except Exception as e:
            log("  requête", mot, "->", e)
            META["erreurs"].append(f"BOAMP '{mot}': {str(e)[:200]}")
            continue
        log(f"  '{mot}' : {len(rows)} avis")
        for x in rows:
            recs[x.get("idweb") or x.get("id")] = x
    return list(recs.values())


def est_resultat(x):
    n = norm(f"{x.get('nature')} {x.get('nature_libelle')}")
    return "resultat" in n or "attribution" in n


@step("Marchés publics (BOAMP)")
def collect_marches():
    depuis = TODAY - dt.timedelta(days=CFG["periodes"]["marches_jours"])
    rows = fetch_boamp(None, depuis)
    if rows:
        log("  champs disponibles :", sorted(rows[0].keys()))
    out = []
    for x in rows:
        objet = x.get("objet") or ""
        if est_resultat(x) or "rectificatif" in norm(x.get("nature_libelle")) or "annulation" in norm(x.get("nature_libelle")):
            continue
        desc = " ".join(as_list(x.get("descripteur_libelle")))
        if HORS_BATIMENT.search(norm(objet)) and not re.search(r"batiment|construction|rehabilitation|logement", norm(objet)):
            continue
        mis = missions(objet + " " + desc)
        if not mis:
            continue
        info = analyse_avis(x)
        lieu, approx = localise(x, info)
        dkm = dist(lieu["lat"], lieu["lon"]) if lieu else None
        eco_seule = mis == ["Économie"]
        ok, raison = dans_zone(dkm, lieu["lat"] if lieu else None, info["montant"], eco_seule)
        if not ok:
            continue
        lim = (x.get("datelimitereponse") or "")[:10]
        ouvert = bool(lim) and lim >= TODAY.isoformat()
        if "Maîtrise d'œuvre" in mis and not any(m in mis for m in ("AMO", "OPC")):
            etape = "Concours / consultation de maîtrise d'œuvre"
        elif "AMO" in mis:
            etape = "Amont : programmation / AMO"
        else:
            etape = "Consultation OPC / DET / économie"
        dep = lieu["dep"] if lieu else None
        dec = maire_de_acheteur(x.get("nomacheteur") or "", dep)
        out.append({
            "id": f"B{x.get('idweb')}",
            "source": "BOAMP",
            "objet": objet,
            "acheteur": x.get("nomacheteur"),
            "decideur": dec,
            "contact": info["contact"],
            "missions": mis,
            "type": type_bat(objet),
            "montant": info["montant"],
            "lieu": lieu["nom"] if lieu else None,
            "dep": dep,
            "distance": dkm,
            "distance_approx": approx,
            "zone": raison,
            "parution": (x.get("dateparution") or "")[:10],
            "limite": lim or None,
            "ouvert": ouvert,
            "etape": etape,
            "procedure": x.get("procedure_libelle"),
            "url": x.get("url_avis") or f"https://www.boamp.fr/pages/avis/?q=idweb:%22{x.get('idweb')}%22",
        })
    out.sort(key=lambda r: (not r["ouvert"], r["limite"] or "9999", r["distance"] or 999))
    save("marches.json", out)
    META.setdefault("nombres", {})["marches"] = len(out)


ATTRIB = []


@step("Attributions de maîtrise d'œuvre (BOAMP)")
def collect_attributions():
    depuis = TODAY - dt.timedelta(days=365 * CFG["periodes"]["attributions_annees"])
    deps = " OR ".join(f"code_departement=\"{d}\"" for d in CFG["departements_recurrence"])
    rows = fetch_boamp(deps, depuis)
    for x in rows:
        if not est_resultat(x):
            continue
        objet = x.get("objet") or ""
        if HORS_BATIMENT.search(norm(objet)) and not re.search(r"batiment|construction|rehabilitation|logement", norm(objet)):
            continue
        mis = missions(objet + " " + " ".join(as_list(x.get("descripteur_libelle"))))
        if not mis:
            continue
        info = analyse_avis(x)
        ATTRIB.append({
            "objet": objet, "acheteur": x.get("nomacheteur"), "missions": mis,
            "titulaires": info["titulaires"], "date": (x.get("dateparution") or "")[:10],
            "dep": (as_list(x.get("code_departement")) or [None])[0], "url": x.get("url_avis"),
        })
    log(f"  {len(ATTRIB)} attributions, dont {sum(1 for a in ATTRIB if a['titulaires'])} avec titulaire identifié")


# ---------------------------------------------------------------- Sitadel
SITADEL_DS = "689c42fa521ccf80ce954f83"
PERMIS, RECUR_MO = [], {}


def dido_params(url):
    """L'API DiDo demande des paramètres (noms de colonnes, millésime)."""
    base = {"withColumnName": "true", "withColumnDescription": "false", "withColumnUnit": "false"}
    tries = [base]
    m = re.search(r"/datafiles/([0-9a-f-]{36})", url)
    if m:
        try:
            meta = get(f"https://data.statistiques.developpement-durable.gouv.fr/dido/api/v1/datafiles/{m.group(1)}").json()
            mils = meta.get("millesimes") or []
            log("  millésimes :", [x.get("millesime") for x in mils][-3:])
            if mils:
                last = sorted(mils, key=lambda x: str(x.get("millesime")))[-1].get("millesime")
                tries.insert(0, dict(base, millesime=last))
        except Exception as e:
            log("  métadonnées DiDo indisponibles :", e)
    # millésimes récents (le plus récent peut être en cours de publication)
    y, mo = TODAY.year, TODAY.month
    for _ in range(4):
        tries.append(dict(base, millesime=f"{y}-{mo:02d}"))
        mo -= 1
        if mo == 0:
            y, mo = y - 1, 12
    return tries + [{}]


def download(url, dest):
    if os.path.exists(dest) and os.path.getsize(dest) > 1000:
        return dest
    for params in dido_params(url):
        log("  téléchargement", url, params)
        with get(url, params=params, stream=True, timeout=900) as r:
            if not r.ok:
                log("  refus", r.status_code, r.text[:400])
                continue
            with open(dest, "wb") as f:
                for chunk in r.iter_content(1 << 20):
                    f.write(chunk)
        log(f"  {os.path.getsize(dest) / 1e6:.0f} Mo")
        return dest
    raise RuntimeError("téléchargement Sitadel refusé pour tous les paramètres essayés")


def open_text(path):
    with open(path, "rb") as f:
        head = f.read(4)
    if head.startswith(b"PK"):
        z = zipfile.ZipFile(path)
        name = max(z.namelist(), key=lambda n: z.getinfo(n).file_size)
        raw = z.open(name)
    elif head.startswith(b"\x1f\x8b"):
        raw = gzip.open(path)
    else:
        raw = open(path, "rb")
    sample = raw.read(200000)
    raw.close()
    enc = "utf-8-sig"
    try:
        sample.decode("utf-8")
    except UnicodeDecodeError:
        enc = "latin-1"
    # ré-ouverture en texte
    if head.startswith(b"PK"):
        return io.TextIOWrapper(zipfile.ZipFile(path).open(name), encoding=enc, errors="replace")
    if head.startswith(b"\x1f\x8b"):
        return io.TextIOWrapper(gzip.open(path), encoding=enc, errors="replace")
    return open(path, encoding=enc, errors="replace", newline="")


def fnum(v):
    try:
        return float(str(v).replace(",", ".")) if v not in (None, "") else 0.0
    except ValueError:
        return 0.0


def pdate(v):
    v = (v or "").strip()
    for fmt in ("%Y-%m-%d", "%d/%m/%Y", "%Y-%m"):
        try:
            return dt.datetime.strptime(v[:10] if fmt != "%Y-%m" else v[:7], fmt).date()
        except ValueError:
            pass
    return None


DEST_MAP = [("HEB", "Hébergement / hôtellerie"), ("BUR", "Tertiaire / bureaux"), ("COM", "Commercial"),
            ("ART", "Industriel / artisanal"), ("IND", "Industriel / artisanal"), ("ENT", "Entrepôt / logistique"),
            ("AGR", "Agricole"), ("EXP", "Agricole"), ("PUB", "Équipement public"), ("SP", "Équipement public"),
            ("CINAPS", "Équipement public"), ("RESTAU", "Commercial"), ("SERV", "Tertiaire / bureaux")]
ETATS = {"2": "Permis accordé", "4": "Annulé", "5": "Chantier ouvert", "6": "Chantier terminé"}


def traite_sitadel(path, kind):
    fh = open_text(path)
    first = fh.readline()
    sep = ";" if first.count(";") >= first.count(",") else ","
    cols = [c.strip().strip('"').upper() for c in next(csv.reader([first], delimiter=sep))]
    log(f"  [{kind}] {len(cols)} colonnes : {cols}")
    rd = csv.reader(fh, delimiter=sep)
    ix = {c: i for i, c in enumerate(cols)}

    def pick(*cands):
        for c in cands:
            if c in ix:
                return ix[c]
        for c in cands:
            for k in ix:
                if k.startswith(c):
                    return ix[k]
        return None

    I = {k: pick(*v) for k, v in {
        "comm": ("COMM", "COM_CODE", "CODE_COMMUNE", "INSEE_COM"),
        "etat": ("ETAT_DAU", "ETAT"),
        "type": ("TYPE_DAU",),
        "num": ("NUM_DAU",),
        "daut": ("DATE_REELLE_AUTORISATION", "DATE_AUTORISATION", "DPC_AUT"),
        "ddoc": ("DATE_REELLE_DOC", "DATE_DOC"),
        "dact": ("DATE_REELLE_DAACT", "DATE_DAACT"),
        "cat": ("CAT_DEM",),
        "siren": ("SIREN_DEM", "SIREN"),
        "siret": ("SIRET_DEM",),
        "denom": ("DENOM_DEM", "DENOMINATION_DEM", "RAISON_SOCIALE_DEM"),
        "nat": ("NATURE_PROJET_COMPLETEE", "NATURE_PROJET_DECLAREE", "NATURE_PROJET"),
        "nblog": ("NB_LGT_TOT_CREES", "NB_LGT_CREES"),
        "typlog": ("TYPE_PRINCIP_LOGTS_CREES", "TYPE_LGT"),
        "shab": ("SURF_HAB_CREEE",),
        "sloc": ("SURF_LOC_CREEE",),
        "num_ter": ("ADR_NUM_TER",), "voie_ter": ("ADR_LIBVOIE_TER",), "typv_ter": ("ADR_TYPEVOIE_TER",),
        "loc_ter": ("ADR_LOCALITE_TER",), "cp_ter": ("ADR_CODPOST_TER",),
        "dest": ("DESTINATION_PRINCIPALE", "DEST_PRINC"),
        "archi": ("REC_ARCHI",),
    }.items()}
    log(f"  [{kind}] correspondances : { {k: (cols[v] if v is not None else None) for k, v in I.items()} }")
    surf_cols = [(i, c) for c, i in ix.items() if c.startswith("SURF_") and ("CREE" in c or "TRANSFO" in c) and "DEMOL" not in c]

    def g(row, k):
        i = I[k]
        return row[i].strip() if i is not None and i < len(row) else ""

    lim_rec = TODAY - dt.timedelta(days=365 * CFG["periodes"]["recurrence_annees"])
    lim_per = TODAY - dt.timedelta(days=365 * CFG["periodes"]["permis_annees"])
    n = kept = 0
    for row in rd:
        n += 1
        if g(row, "type") and g(row, "type").upper() != "PC":
            continue
        siren = re.sub(r"\D", "", g(row, "siren") or g(row, "siret"))[:9]
        if len(siren) != 9:
            continue  # particulier ou demandeur anonymisé
        daut = pdate(g(row, "daut"))
        if not daut or daut < lim_rec:
            continue
        etat = g(row, "etat")
        if etat == "4":
            continue
        com = commune_info(g(row, "comm"))
        dkm = dist(com["lat"], com["lon"]) if com else None
        # surface et type
        nat = g(row, "nat")
        rehab = nat == "2"
        def col_sum(*names):
            return sum(fnum(row[ix[c]]) for c in names if c in ix and ix[c] < len(row))
        if kind == "logements":
            if col_sum("NB_LGT_COL_CREES", "NB_LGT_RES") == 0 and col_sum("NB_LGT_IND_CREES") > 0:
                continue  # uniquement de l'individuel
            surf = col_sum("SURF_HAB_CREEE", "SURF_HAB_ISSUE_TRANSFO") or (col_sum("SURF_HAB_TRANSFORMEE") if rehab else 0)
            typ = "Résidence (étudiants, seniors…)" if col_sum("NB_LGT_RES") > col_sum("NB_LGT_COL_HORS_RES") else "Logement collectif"
        else:
            parts = {}
            for i, c in surf_cols:
                if c.startswith(("SURF_LOC", "SURF_HAB")) or c.endswith("TRANSFORMEE"):
                    continue
                v = fnum(row[i]) if i < len(row) else 0
                if v > 0:
                    lab = next((lab for key, lab in DEST_MAP if c.startswith(f"SURF_{key}")), "Autre")
                    parts[lab] = parts.get(lab, 0) + v
            surf = col_sum("SURF_LOC_CREEE", "SURF_LOC_ISSUE_TRANSFO") or sum(parts.values())
            if not surf and rehab:
                surf = col_sum("SURF_LOC_TRANSFORMEE")
            typ = max(parts, key=parts.get) if parts else "Autre"
        cout = CFG["cout_m2_eur"].get(typ, CFG["cout_m2_eur"]["Autre"]) * (CFG["coef_rehabilitation"] if rehab else 1)
        montant = round(surf * cout, -3) if surf > 0 else None
        # récurrence (projets d'au moins 150 k€ estimés)
        if (montant or 0) < 150_000:
            if daut < lim_per:
                continue
            r = {"total": 0, "zone": 0, "montant_zone": 0, "derniere": ""}
        else:
            r = None
        r = r or RECUR_MO.setdefault(siren, {"siren": siren, "nom": g(row, "denom"), "total": 0, "zone": 0, "montant_zone": 0, "derniere": ""})
        r["total"] += 1
        if dkm is not None and dkm <= Z["moyen_projet_rayon_km"]:
            r["zone"] += 1
            r["montant_zone"] += montant or 0
        r["derniere"] = max(r["derniere"], daut.isoformat())
        if daut < lim_per:
            continue
        ok, raison = dans_zone(dkm, com["lat"] if com else None, montant)
        if not ok:
            continue
        kept += 1
        adr = " ".join(filter(None, [g(row, "num_ter"), g(row, "typv_ter"), g(row, "voie_ter")])).strip()
        ddoc, dact = pdate(g(row, "ddoc")), pdate(g(row, "dact"))
        etape = ("Chantier terminé" if (dact or etat == "6") else
                 "Chantier ouvert" if (ddoc or etat == "5") else "Permis accordé, chantier non ouvert")
        PERMIS.append({
            "id": f"P{g(row, 'num') or n}",
            "source": "Permis",
            "num": g(row, "num"),
            "siren": siren,
            "mo": g(row, "denom"),
            "type": typ,
            "rehab": rehab,
            "surface": round(surf) if surf else None,
            "logements": int(fnum(g(row, "nblog"))) or None,
            "montant": montant,
            "lieu": com["nom"] if com else g(row, "loc_ter"),
            "adresse": adr or None,
            "dep": com["dep"] if com else None,
            "distance": dkm,
            "zone": raison,
            "autorise": daut.isoformat(),
            "ouverture": ddoc.isoformat() if ddoc else None,
            "achevement": dact.isoformat() if dact else None,
            "etape": etape,
            "architecte": {"1": True, "O": True, "0": False, "N": False}.get(g(row, "archi").upper()),
        })
    log(f"  [{kind}] {n} lignes lues, {kept} permis retenus")


@step("Permis de construire (Sitadel)")
def collect_permis():
    r = get(f"https://www.data.gouv.fr/api/1/datasets/{SITADEL_DS}/")
    r.raise_for_status()
    res = r.json().get("resources", [])
    for x in res:
        log("  ressource :", x.get("title"), "|", x.get("format"), "|", x.get("url"))
    def find(word):
        cands = [x for x in res if word in norm(x.get("title")) and "demol" not in norm(x.get("title"))
                 and "amenag" not in norm(x.get("title")) and (x.get("format") or "").lower() in ("csv", "zip", "gz", "")]
        cands = [x for x in cands if "dictionnaire" not in norm(x.get("title")) and "variables" not in norm(x.get("title"))] or cands
        return cands[0] if cands else None
    for word, kind in (("locaux", "locaux"), ("logement", "logements")):
        x = find(word)
        if not x:
            raise RuntimeError(f"ressource '{word}' introuvable")
        path = download(x["url"], os.path.join(WORK, f"sitadel_{kind}"))
        traite_sitadel(path, kind)
    seen, uniq = set(), []
    for p in sorted(PERMIS, key=lambda p: p["autorise"], reverse=True):
        k = (p["num"], p["type"])
        if k in seen:
            continue
        seen.add(k)
        uniq.append(p)
    PERMIS[:] = uniq
    log(f"  {len(PERMIS)} permis au total")


# ---------------------------------------------------------------- architectes
ARCHIS = []


@step("Agences d'architecture (annuaire des entreprises)")
def collect_architectes():
    for dep in CFG["departements_architectes"]:
        page = 1
        while True:
            time.sleep(0.16)
            r = get("https://recherche-entreprises.api.gouv.fr/search", params={
                "activite_principale": "71.11Z", "departement": dep, "etat_administratif": "A",
                "per_page": 25, "page": page})
            if not r.ok:
                log("  archis", dep, r.status_code, r.text[:200])
                break
            j = r.json()
            for x in j.get("results", []):
                e = ent_from_result(x)
                ENT[e["siren"]] = e
                ARCHIS.append(e["siren"])
            if page >= (j.get("total_pages") or 1) or page >= 60:
                break
            page += 1
        log(f"  dép. {dep} : {len(ARCHIS)} cumulés")


# ---------------------------------------------------------------- assemblage
@step("Clients récurrents et enrichissement")
def assemble():
    # architectes / titulaires récurrents des marchés publics
    tit = {}
    for a in ATTRIB:
        if "Maîtrise d'œuvre" not in a["missions"]:
            continue
        for t in a["titulaires"][:1]:  # le mandataire
            k = norm(t)
            e = tit.setdefault(k, {"nom": t, "n": 0, "acheteurs": set(), "derniere": "", "deps": set(), "exemples": []})
            e["n"] += 1
            e["acheteurs"].add(a["acheteur"])
            e["deps"].add(a["dep"])
            e["derniere"] = max(e["derniere"], a["date"])
            if len(e["exemples"]) < 5:
                e["exemples"].append({"objet": a["objet"], "acheteur": a["acheteur"], "date": a["date"], "url": a["url"]})
    titulaires = sorted(tit.values(), key=lambda e: -e["n"])[:200]
    for e in titulaires:
        e["siren"] = siren_par_nom(e["nom"], sorted(e["deps"])[0] if e["deps"] else None)
        e["acheteurs"] = sorted(x for x in e["acheteurs"] if x)
        e["deps"] = sorted(x for x in e["deps"] if x)

    # acheteurs publics récurrents
    ach = {}
    for a in ATTRIB:
        k = norm(a["acheteur"])
        e = ach.setdefault(k, {"nom": a["acheteur"], "n": 0, "missions": {}, "derniere": "", "dep": a["dep"]})
        e["n"] += 1
        for m in a["missions"]:
            e["missions"][m] = e["missions"].get(m, 0) + 1
        e["derniere"] = max(e["derniere"], a["date"])
    acheteurs = sorted((e for e in ach.values() if e["n"] >= 2), key=lambda e: -e["n"])[:300]
    for e in acheteurs:
        e["decideur"] = maire_de_acheteur(e["nom"] or "", e["dep"])

    # maîtres d'ouvrage privés récurrents
    mos = sorted((r for r in RECUR_MO.values() if r["zone"] >= 2), key=lambda r: (-r["zone"], -r["total"]))[:400]

    # enrichissement dirigeants
    for s in [p["siren"] for p in PERMIS] + [m["siren"] for m in mos]:
        entreprise(s)

    archis = []
    tit_by_siren = {e["siren"]: e for e in titulaires if e.get("siren")}
    tit_by_name = {norm(e["nom"]): e for e in titulaires}
    for s in dict.fromkeys(ARCHIS):
        e = ENT.get(s) or {}
        dkm = dist(e.get("lat"), e.get("lon"))
        if dkm is None or dkm > Z["moyen_projet_rayon_km"]:
            continue
        t = tit_by_siren.get(s) or tit_by_name.get(norm(e.get("nom")))
        archis.append({"siren": s, "distance": dkm, "marches": t["n"] if t else 0,
                       "derniere": t["derniere"] if t else None})
    archis.sort(key=lambda a: (-a["marches"], a["distance"]))

    # nombre de permis du MO sur chaque fiche
    for p in PERMIS:
        r = RECUR_MO.get(p["siren"]) or {}
        p["mo_permis_zone"] = r.get("zone", 0)
        p["mo_permis_total"] = r.get("total", 0)

    used = set(p["siren"] for p in PERMIS) | set(m["siren"] for m in mos) | set(a["siren"] for a in archis) \
        | set(e["siren"] for e in titulaires if e.get("siren"))
    save("permis.json", PERMIS)
    save("recurrents.json", {"maitres_ouvrage": mos, "titulaires": titulaires, "acheteurs": acheteurs})
    save("architectes.json", archis)
    save("entreprises.json", {s: ENT[s] for s in used if s in ENT})


def main():
    load_communes()
    load_maires()
    collect_marches()
    collect_attributions()
    collect_permis()
    collect_architectes()
    assemble()
    with open(ENT_CACHE_F, "w", encoding="utf-8") as f:
        json.dump(ENT, f, ensure_ascii=False)
    with open(NAME_CACHE_F, "w", encoding="utf-8") as f:
        json.dump(NAMES, f, ensure_ascii=False)
    META["config"] = {"base": BASE, "regles_zone": Z}
    META["diagnostic_avis"] = DIAG
    save("meta.json", META)
    log("\nErreurs :", META["erreurs"] or "aucune")


if __name__ == "__main__":
    main()
