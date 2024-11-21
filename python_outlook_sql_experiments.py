import os
import re
import cv2
import sys
import json
import json
import nltk
import tqdm
import spacy
import codecs
import os,sys
import pyodbc
import string
import hashlib
import keyring
import logging
import requests
import traceback
import matplotlib
import extract_msg
import numpy as np
import pandas as pd
from tqdm import tqdm
from colormod import *
from io import BytesIO
import PySimpleGUI as sg
from time import sleep
from github import Auth
import pypdfium2 as pdfium
from github import Github
from timeit import timeit
from spacy import displacy
from spacy import tokenizer
from termcolor import cprint
from outlook_msg import Message
from unidecode import unidecode
from dataclasses import dataclass
from dateutil.parser import parse
from nltk.corpus import stopwords
from types import SimpleNamespace
from datetime import datetime, timezone
from nltk.tokenize import word_tokenize
from PIL import Image,ImageOps,ImageFile
from requests import Response, ConnectionError
from requests.adapters import HTTPAdapter, Retry
from datetime import datetime as dt, timedelta as td
from traceback_with_variables import activate_by_import
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import Annotated, Any, AnyStr, Callable, Dict, get_type_hints, Generic, Generator, List, NewType, Optional, Tuple


nltk.download("punkt",quiet=True)
nltk.download("stopwords",quiet=True)
nltk.download("tagsets",quiet=True)
sw = set(stopwords.words("english"))
nlp = spacy.load('en_core_web_sm')
ImageFile.LOAD_TRUNCATED_IMAGES = True
logging.basicConfig(filename="./re-test_sqlite3.log", encoding="utf-8", level=logging.DEBUG)


@dataclass(frozen=False)
class c:
    file_path=""
    save_to_path =""
    email_files = []
    img_files = []
    emails = {}
    msg_class_types = [ 'IPM.Note','IPM.Appointment','IPM.Schedule.Meeting.Canceled', 'IPM.Schedule.Meeting.Request']    
    ld = {}
    _ld = lambda x: { c.ld[k]:v for k, v in dict(x).items() }
    _lh = lambda x: list([dict(x)[k]['url'] for k, v in dict(x).items()])
    now = lambda: datetime.strftime(datetime.now(), r"%Y%m%d%H%M%S")
    _hex_chk = lambda x: str(''.join(l for l in [x for x in str(x).replace(chr(32),chr(95))] if l in set('ABCDEF0123456789')))
    fn_rm = lambda s: str(''.join(
        l for l in [x for x in str(s).replace(chr(32),chr(95))] 
        if l in set('abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-.')))
    np_k2_ord_srt = lambda npl: [ 
                        x for x in [np.array(c)[0:].reshape(-1) for c in [ np.array(f[np.argsort(g)]).astype('str').tolist()
                        for f,g in [np.unique(np.array([[str(x[0]).split(chr(32))
                        for x in sorted([[s,npl.count(s)] 
                        for s in [ np.array(y[np.argsort(z)]).astype('str').tolist()[0]
                        for y,z in [np.unique(np.array(npl),return_index=True)]]],
                        key=lambda x: x[1], reverse=False)]]),return_index=True)]]]]
    rm_sp = lambda s: str(re.sub('\s+', ' ', (re.sub('_', '', (re.sub('[^a-zA-z0-9\s]', '', unidecode(str(s))))))).strip().lower())
    rm_aw = lambda s: "".join(str(s).split())
    rm_sw = lambda s: str(' '.join(w for w in word_tokenize(str(s)) if w not in sw))
    rm_wh = lambda s: " ".join(str(s).split())
    rm_pu = lambda s: str(s).translate(str.maketrans('', '', string.punctuation))

    def __post_init__(self):
        self.file_path = c.file_path
        self.save_to_path  = c.save_to_path 
        self.email_files  = c.email_files 
        self.img_files  = c.img_files 
        self.msg_class_types  = c.msg_class_types 
        self.ld  = c.ld 
        self._ld  = c._ld 
        self._lh  = c._lh 
        self.now  = c.now 
        self._hex_chk  = c._hex_chk 
        self.fn_rm  = c.fn_rm 
        self.np_k2_ord_srt  = c.np_k2_ord_srt 
        self.rm_sp  = c.rm_sp 
        self.rm_aw  = c.rm_aw 
        self.rm_sw  = c.rm_sw 
        self.rm_wh  = c.rm_wh 
        self.rm_pu  = c.rm_pu 
        super().__setattr__("attr_name", self)

    @staticmethod
    def dns(d:dict) -> SimpleNamespace:
        return SimpleNamespace(**d)


def body_parse(msg_body:str):
    all_words = str("")
    phone_numbers = []
    msg_body_str = str(unidecode(msg_body)).replace('\r\n',' ').lower().replace('\n',' ').replace(r'%0d',' ').replace(r'%0a',' ').replace('<','').replace('>','')
    msg_body_str = str(msg_body_str).replace('\n','').replace('(','').replace(')','-').replace('https://','').replace('htt/mnt/p//','').replace('mailto:','')
    email_addr = np.unique(np.array([x for x in c.rm_wh(msg_body_str).split(' ') if str(x).find('@')!=-1 and str(x).find('.')!=-1 and str(x).find('@')<str(x).find('.')])).tolist()
    phone_numbers1 = np.unique(np.array(re.findall(r"([ ]{1}\d{3}[.+\D\W\s]{1}\d{3}[.+\D\W\s]{1}\d{4}[ ]{1})",str(''.join(str(x)+chr(32) for x in c.rm_wh(msg_body_str).split(' ')))))).tolist()
    phone_numbers2 = np.unique(np.array(re.findall(r"([ ]{1}\d{10}[ ]{1})",str(''.join(str(x)+chr(32) for x in c.rm_wh(msg_body_str).split(' ')))))).tolist()
    whitelist = set('abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ:@-._ ')
    ph_cheat = [phone_numbers.append(str(c.rm_wh(c.rm_sp(x))).replace(chr(32),''))for x in phone_numbers1
                ]+[phone_numbers.append(c.rm_wh(c.rm_sp(x)).replace(chr(32),''))for x in phone_numbers2]
    len(ph_cheat)
    msg_body_stripped = [''.join(str(x)+chr(32) for x in c.rm_wh(msg_body_str).split(' ') if len(x)>2)]
    msg_body_parse = [x for x in msg_body_stripped if len(x)>2]
    for p in msg_body_parse:
            all_words = str(all_words) + str(p) + chr(32)
    spacy_nlp = nlp(all_words)
    ner = [(n.text,n.start_char,n.end_char, n.label_) for n in spacy_nlp.ents]
    ner_list = []
    ner_list=[ [list(x)[3],list(x)[0]] for x in ner]
    text_tokens = word_tokenize(all_words)
    stops = stopwords.words('english')
    no_stop_words = [s for s in text_tokens if s.lower() not in stops and not len(s) < 2]
    all_uniques = np.unique(np.array(no_stop_words)).tolist()
    whitelist = set('abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ')
    msg_body_stripped = [''.join(l for l in str(x)+chr(32) if l in whitelist) for x in c.rm_wh(msg_body).split(' ')  if len(x)>2]
    msg_body_parse = [x for x in msg_body_stripped 
                      if len(x)>2
                      and str(x).find(r"http")==-1
                      and str(x).find(r"mailto")==-1
                      and str(x).find(r"www")==-1
                      and str(x).find(r"mailto")==-1
                      and str(x)[-3:]!=r"com"
                      ]
    msg_body_uniq = np.unique(np.array(msg_body_parse)).tolist()
    for p in msg_body_uniq:
            all_words = all_words + p + " "
    tt = word_tokenize(all_words)
    nsw = [s for s in tt if s.lower() not in stops and not len(s) < 2]
    unique_words = np.unique(np.array(nsw)).tolist()
    return all_uniques, unique_words, phone_numbers, email_addr, ner_list

def SQL_insert_list(sql:str,emails:list):
    sql = str(r"")
    sql_ids_query = str(r"")
    all_uniques_pk=str(r"")
    unique_words_pk=str(r"")
    phone_numbers_pk=str(r"")
    email_addresses_pk=str(r"")
    attachments_pk=str(r"")
    named_entities_pk=str(r"")
    for eml in tqdm(emails,desc="INSERT INTO SQL: "):
        if eml['filename'] is None:
            sql_filename = str(r"NULL")
        else:
            sql_filename=eml['filename']
        if eml['file_id'] is None:
            sql_file_id = str(r"NULL")
        else:
            sql_file_id=eml['file_id']
        if eml['date'] is None:
            sql_date = str(r"NULL")
        else:
            sql_date=eml['date']
        if eml['msg_class'] is None:
            sql_msg_class = str(r"NULL")
        else:
            sql_msg_class=eml['msg_class']
        if eml['body_md5'] is None:
            sql_body_md5 = str(r"NULL")
        else:
            sql_body_md5=eml['body_md5']
        if eml['body'] is None:
            sql_body = str(r"NULL")
        else:
            sql_body=eml['body']
        if eml['sender'] is None:
            sql_sender = str(r"NULL")
        else:
            sql_sender=eml['sender']
        if eml['to'] is None:sql_to = str(r"NULL")
        else:
            sql_to=eml['to']
        if eml['message_id'] is None:
            sql_message_id = str(r"NULL")
        else:
            sql_message_id=eml['message_id']
        if eml['header'] is None:
            sql_header = str(r"NULL")
        else:
            sql_header=eml['header']
        if eml['subject'] is None:
            sql_subject = str(r"NULL")
        else:
            sql_subject=eml['subject']
        if eml['cc'] is None:
            sql_cc = str(r"NULL")
        else:
            sql_cc=eml['cc']
        if eml['bcc'] is None:
            sql_bcc = str(r"NULL")
        else:
            sql_bcc=eml['bcc']
        if eml['named_entities'] is None:
            sql_named_entities = str(r"NULL")
        else:
            sql_named_entities=eml['named_entities'] 
        insert_filename=unidecode(str(sql_filename)).replace(chr(39),str(r'&#39')).lower()
        insert_file_id=unidecode(str(sql_file_id)).replace(chr(39),str(r'&#39')).upper()
        insert_date=unidecode(str(sql_date)).replace(chr(39),str(r'&#39'))
        insert_msg_class=unidecode(str(sql_msg_class)).replace(chr(39),str(r'&#39'))
        insert_body_md5=unidecode(str(sql_body_md5)).replace(chr(39),str(r'&#39')).upper()
        insert_body=unidecode(str(sql_body)).replace(chr(39),str(r'&#39'))
        insert_sender=unidecode(str(sql_sender)).replace(chr(39),str(r'&#39'))
        insert_to=unidecode(str(sql_to)).replace(chr(39),str(r'&#39'))
        insert_message_id=unidecode(str(sql_message_id)).replace(chr(39),str(r'&#39'))
        insert_header=unidecode(str(sql_header)).replace(chr(39),str(r'&#39'))
        insert_subject=unidecode(str(sql_subject)).replace(chr(39),str(r'&#39'))
        insert_cc=unidecode(str(sql_cc)).replace(chr(39),str(r'&#39'))
        insert_bcc=unidecode(str(sql_bcc)).replace(chr(39),str(r'&#39'))
        sql = sql + str(r"INSERT INTO email([filename],[file_id],[date],[msg_class],[body_md5],[body],[sender],[to],[message_id],[header],[subject],[cc],[bcc])")
        sql = sql + str(f"VALUES('{insert_filename}','{insert_file_id}','{insert_date}','{insert_msg_class}','{insert_body_md5}','{insert_body}','{insert_sender}',")
        sql = sql + str(f"'{insert_to}','{insert_message_id}','{insert_header}','{insert_subject}','{insert_cc}','{insert_bcc}')")
        conn = pyodbc.connect("DRIVER={ODBC Driver 17 for SQL Server};SERVER=" + str(server) + ";DATABASE="+str(database)+";UID="+str(username)+";PWD="+ str(password))
        cursor = conn.cursor()
        cursor.execute(sql)
        conn.commit()
        sql_ids_query = str(f"select all_uniques_pk, unique_words_pk, phone_numbers_pk, email_addresses_pk, attachments_pk, named_entities_pk from email where file_id = '{str(sql_file_id)}'")
        rows = cursor.execute(sql_ids_query).fetchall()
        for row in rows:
                all_uniques_pk = row.all_uniques_pk
                unique_words_pk = row.unique_words_pk
                phone_numbers_pk = row.phone_numbers_pk
                email_addresses_pk = row.email_addresses_pk
                attachments_pk = row.attachments_pk
                named_entities_pk = row.named_entities_pk
        conn.commit()
        sql = str(r"")
        if str(eml['all_uniques']) is str("[]") or len(eml['all_uniques'])==0:
            sql_all_uniques = str(r"NULL")
            sql = sql + str(f"insert into all_uniques(email,word) values('{all_uniques_pk}',")
            sql = sql + str(f"'{str(sql_all_uniques).replace(chr(39),str(r'&#39')).replace(chr(39),str(r'&#39'))}')")+str(chr(10))
        else:
            sql_all_uniques=eml['all_uniques']
            for au_val in sql_all_uniques:
                sql = sql + str(f"insert into all_uniques(email,word) values('{all_uniques_pk}',")
                sql = sql + str(f"'{str(au_val).replace(chr(39),str(r'&#39'))}')") +str(chr(10))
        if str(eml['unique_words']) is str("[]") or len(eml['unique_words'])==0:
            sql_unique_words = str(r"NULL")
            sql = sql + str(f"insert into unique_words(email,word) values('{unique_words_pk}',")
            sql = sql + str(f"'{str(sql_unique_words).replace(chr(39),str(r'&#39')).replace(chr(39),str(r'&#39'))}')")+str(chr(10))
        else:
            sql_unique_words=eml['unique_words']
            for uw_val in sql_unique_words:
                sql = sql + str(f"insert into unique_words(email,word) values('{unique_words_pk}',")
                sql = sql + str(f"'{str(uw_val).replace(chr(39),str(r'&#39'))}')")+str(chr(10)) 
        if str(eml['phone_numbers']) is str("[]") or len(eml['phone_numbers'])==0:
            sql_phone_numbers = str(r"NULL")
            sql = sql + str(f"insert into phone_numbers(email,phone_no) values('{phone_numbers_pk}',")
            sql = sql + str(f"'{str(sql_phone_numbers).replace(chr(39),str(r'&#39')).replace(chr(39),str(r'&#39'))}')")+str(chr(10))
        else:
            sql_phone_numbers=eml['phone_numbers']
            for ph_val in sql_phone_numbers:
                sql = sql + str(f"insert into phone_numbers(email,phone_no) values('{phone_numbers_pk}',")
                sql = sql + str(f"'{str(ph_val).replace(chr(39),str(r'&#39'))}')")+str(chr(10)) 
        if str(eml['email_addresses']) is str("[]") or len(eml['email_addresses'])==0:
            sql_email_addresses = str(r"NULL")
            sql = sql + str(f"insert into email_addresses(email,email_address) values('{email_addresses_pk}',")
            sql = sql + str(f"'{str(sql_email_addresses).replace(chr(39),str(r'&#39')).replace(chr(39),str(r'&#39'))}')")+str(chr(10))
        else:
            sql_email_addresses=eml['email_addresses']
            for emailaddr_val in sql_email_addresses:
                sql = sql + str(f"insert into email_addresses(email,email_address) values('{email_addresses_pk}',")
                sql = sql + str(f"'{str(emailaddr_val).replace(chr(39),str(r'&#39'))}')")+str(chr(10)) 
        if str(eml['attachments']) is str("[]") or len(eml['attachments'])==0:
            sql_attachments = str(r"NULL")
            sql = sql + str(f"insert into attachments(email,attachment) values('{attachments_pk}',")
            sql = sql + str(f"'{str(sql_attachments).replace(chr(39),str(r'&#39')).replace(chr(39),str(r'&#39'))}')")+str(chr(10))
        else:
            sql_attachments=eml['attachments']
            for sql_val in sql_attachments:
                sql = sql + str(f"insert into attachments(email,attachment) values('{attachments_pk}',")
                sql = sql + str(f"'{str(sql_val).replace(chr(39),str(r'&#39'))}')")+str(chr(10))
        if str(eml['named_entities']) is str("[]") or len(eml['named_entities'])==0:
            sql_named_entities = str(r"NULL")
            sql = sql + str(f"insert into named_entities(email,type,entity) values('{named_entities_pk}',")
            sql = sql + str(f"'{str(sql_named_entities).replace(chr(39),str(r'&#39')).replace(chr(39),str(r'&#39'))}',")+str(chr(10))
            sql = sql + str(f"'{str(sql_named_entities).replace(chr(39),str(r'&#39')).replace(chr(39),str(r'&#39'))}')")+str(chr(10))
        else:
            sql_named_entities=eml['named_entities']
            for ner_val in  sql_named_entities:
                sql = sql + str(f"insert into named_entities(email,type,entity) values('{named_entities_pk}',")
                sql = sql + str(f"'{str(ner_val[0]).replace(chr(39),str(r'&#39'))}',")
                sql = sql + str(f"'{str(ner_val[1]).replace(chr(39),str(r'&#39'))}')")+str(chr(10))
        # with open(f"/mnt/p/msg/eml_sql.sql","a") as fi:
        #     fi.write(str(unidecode(sql))+'\n')
        cursor.execute(sql)
        conn.commit()

def msg_proc(f,sql):
    f_id = str(os.path.basename(f)).replace(f[-(f[::-1].find('.'))-1:],'')
    msg = extract_msg.Message(f)
    msg_body = str(msg.body)
    all_uniques, unique_words, phone_numbers, email_addr, ner_list = body_parse(msg_body)
    msg_body = c.rm_wh(str(msg_body).replace(chr(34),'').replace(chr(39),'').replace('\r\n',' ').replace('\n',' ').replace(f'\\r\\n',' ').replace(f'\\n',' '))
    msg_body_bytes = bytes(str(f"{msg.body}"),encoding='utf-8')
    body_md5 = str(hashlib.md5(msg_body_bytes).hexdigest())
    if msg.date is not None:
        msg_date = dt.strptime(msg.date, "%a, %d %b %Y %H:%M:%S %z")
        msg_fdate = msg_date.strftime("%Y%m%d%H%M%S")
    elif msg.date is None:
        msg_fdate = str('None')
    msg_attachments = [a.displayName for a in msg.attachments]
    emails.append({
                'filename':f,
                'file_id':f_id,
                'date':msg_fdate,
                'msg_class':msg.classType,
                'body_md5':body_md5,
                'body':msg_body,
                'all_uniques':all_uniques,
                'unique_words':unique_words,
                'phone_numbers':phone_numbers,
                'email_addresses':email_addr,
                'sender':str(msg.sender),
                'to':str(msg.to),
                'message_id':str(msg.messageId),
                'header':str(msg.headerDict),
                'subject':str(msg.subject),
                'cc':str(msg.cc),
                'bcc':str(msg.bcc),
                'attachments':msg_attachments,
                'named_entities':ner_list})
    msg.close()
    return emails,sql

emails=[]
sql = str("")

status_bar = tqdm(total=len(email_files), desc='Parsing Emails')

# for i in range(0,10):
#     msg_proc(email_files[i],sql)
#     status_bar.update(n=1)

# for i in range(0,len(email_files)-1):
#     msg_proc(email_files[i],sql)
#     status_bar.update(n=1)

for f in email_files:
    emails,sql = msg_proc(f,sql)
    status_bar.update(n=1)
SQL_insert_list(sql,emails)

# status_bar = tqdm(total=len(email_files), desc='Parsing Emails')
# with open(f"/mnt/p/msg/eml_sql.sql","wt") as fi:
#             fi.write(str(''))

# def main(sql,email_files):
#     with ThreadPoolExecutor(16) as executor:
#         futures = [executor.submit(msg_proc,f,sql) for f in email_files]
#         for _ in as_completed(futures):
#             status_bar.update(n=1)
#     SQL_insert_list(sql,emails)


# cp_r("FEED ME A STRAY CAT\n")
# main(sql,email_files)
# cp_r("FEED ME A STRAY CAT\n")



def SQL_insert_list(sql:str,emails:list):
    sql = str(r"")
    # sql_ids_query = str(r"")
    all_uniques_pk=str(r"")
    unique_words_pk=str(r"")
    phone_numbers_pk=str(r"")
    email_addresses_pk=str(r"")
    attachments_pk=str(r"")
    named_entities_pk=str(r"")
    for eml in tqdm(emails,desc="INSERT INTO SQL: "):
        if eml['filename'] is None:
            sql_filename = str(r"NULL")
        else:
            sql_filename=eml['filename']
        if eml['file_id'] is None:
            sql_file_id = str(r"NULL")
        else:
            sql_file_id=eml['file_id']
        if eml['date'] is None:
            sql_date = str(r"NULL")
        else:
            sql_date=eml['date']
        if eml['msg_class'] is None:
            sql_msg_class = str(r"NULL")
        else:
            sql_msg_class=eml['msg_class']
        if eml['body_md5'] is None:
            sql_body_md5 = str(r"NULL")
        else:
            sql_body_md5=eml['body_md5']
        if eml['body'] is None:
            sql_body = str(r"NULL")
        else:
            sql_body=eml['body']
        if eml['sender'] is None:
            sql_sender = str(r"NULL")
        else:
            sql_sender=eml['sender']
        if eml['to'] is None:
            sql_to = str(r"NULL")
        else:
            sql_to=eml['to']
        if eml['message_id'] is None:
            sql_message_id = str(r"NULL")
        else:
            sql_message_id=eml['message_id']
        if eml['header'] is None:
            sql_header = str(r"NULL")
        else:
            sql_header=eml['header']
        if eml['subject'] is None:
            sql_subject = str(r"NULL")
        else:
            sql_subject=eml['subject']
        if eml['cc'] is None:
            sql_cc = str(r"NULL")
        else:
            sql_cc=eml['cc']
        if eml['bcc'] is None:
            sql_bcc = str(r"NULL")
        else:
            sql_bcc=eml['bcc']
        if eml['named_entities'] is None:
            sql_named_entities = str(r"NULL")
        else:
            sql_named_entities=eml['named_entities'] 
        insert_filename=unidecode(str(sql_filename)).replace(chr(39),str(r'&#39')).lower()
        insert_file_id=unidecode(str(sql_file_id)).replace(chr(39),str(r'&#39')).upper()
        insert_date=unidecode(str(sql_date)).replace(chr(39),str(r'&#39'))
        insert_msg_class=unidecode(str(sql_msg_class)).replace(chr(39),str(r'&#39'))
        insert_body_md5=unidecode(str(sql_body_md5)).replace(chr(39),str(r'&#39')).upper()
        insert_body=unidecode(str(sql_body)).replace(chr(39),str(r'&#39'))
        insert_sender=unidecode(str(sql_sender)).replace(chr(39),str(r'&#39'))
        insert_to=unidecode(str(sql_to)).replace(chr(39),str(r'&#39'))
        insert_message_id=unidecode(str(sql_message_id)).replace(chr(39),str(r'&#39'))
        insert_header=unidecode(str(sql_header)).replace(chr(39),str(r'&#39'))
        insert_subject=unidecode(str(sql_subject)).replace(chr(39),str(r'&#39'))
        insert_cc=unidecode(str(sql_cc)).replace(chr(39),str(r'&#39'))
        insert_bcc=unidecode(str(sql_bcc)).replace(chr(39),str(r'&#39'))
        sql = sql + str(r"INSERT INTO email([filename],[file_id],[date],[msg_class],[body_md5],[body],[sender],[to],[message_id],[header],[subject],[cc],[bcc])")
        sql = sql + str(f"VALUES('{insert_filename}','{insert_file_id}','{insert_date}','{insert_msg_class}','{insert_body_md5}','{insert_body}','{insert_sender}',")
        sql = sql + str(f"'{insert_to}','{insert_message_id}','{insert_header}','{insert_subject}','{insert_cc}','{insert_bcc}')")
        # conn = pyodbc.connect("DRIVER={ODBC Driver 17 for SQL Server};SERVER=" + str(server) + ";DATABASE="+str(database)+";UID="+str(username)+";PWD="+ str(password))
        # cursor = conn.cursor()
        # cursor.execute(sql)
        # conn.commit()
        # sql_ids_query = str(f"select all_uniques_pk, unique_words_pk, phone_numbers_pk, email_addresses_pk, attachments_pk, named_entities_pk from email where file_id = '{str(sql_file_id)}'")
        # rows = cursor.execute(sql_ids_query).fetchall()
        # for row in rows:
        #         all_uniques_pk = row.all_uniques_pk
        #         unique_words_pk = row.unique_words_pk
        #         phone_numbers_pk = row.phone_numbers_pk
        #         email_addresses_pk = row.email_addresses_pk
        #         attachments_pk = row.attachments_pk
        #         named_entities_pk = row.named_entities_pk
        # conn.commit()
        sql = str(r"")
        if str(eml['all_uniques']) is str("[]") or len(eml['all_uniques'])==0:
            sql_all_uniques = str(r"NULL")
            sql = sql + str(f"insert into all_uniques(email,word) values('{all_uniques_pk}',")
            sql = sql + str(f"'{str(sql_all_uniques).replace(chr(39),str(r'&#39')).replace(chr(39),str(r'&#39'))}')")+str(chr(10))
        else:
            sql_all_uniques=eml['all_uniques']
            for au_val in sql_all_uniques:
                sql = sql + str(f"insert into all_uniques(email,word) values('{all_uniques_pk}',")
                sql = sql + str(f"'{str(au_val).replace(chr(39),str(r'&#39'))}')") +str(chr(10))
        if str(eml['unique_words']) is str("[]") or len(eml['unique_words'])==0:
            sql_unique_words = str(r"NULL")
            sql = sql + str(f"insert into unique_words(email,word) values('{unique_words_pk}',")
            sql = sql + str(f"'{str(sql_unique_words).replace(chr(39),str(r'&#39')).replace(chr(39),str(r'&#39'))}')")+str(chr(10))
        else:
            sql_unique_words=eml['unique_words']
            for uw_val in sql_unique_words:
                sql = sql + str(f"insert into unique_words(email,word) values('{unique_words_pk}',")
                sql = sql + str(f"'{str(uw_val).replace(chr(39),str(r'&#39'))}')")+str(chr(10)) 
        if str(eml['phone_numbers']) is str("[]") or len(eml['phone_numbers'])==0:
            sql_phone_numbers = str(r"NULL")
            sql = sql + str(f"insert into phone_numbers(email,phone_no) values('{phone_numbers_pk}',")
            sql = sql + str(f"'{str(sql_phone_numbers).replace(chr(39),str(r'&#39')).replace(chr(39),str(r'&#39'))}')")+str(chr(10))
        else:
            sql_phone_numbers=eml['phone_numbers']
            for ph_val in sql_phone_numbers:
                sql = sql + str(f"insert into phone_numbers(email,phone_no) values('{phone_numbers_pk}',")
                sql = sql + str(f"'{str(ph_val).replace(chr(39),str(r'&#39'))}')")+str(chr(10)) 
        if str(eml['email_addresses']) is str("[]") or len(eml['email_addresses'])==0:
            sql_email_addresses = str(r"NULL")
            sql = sql + str(f"insert into email_addresses(email,email_address) values('{email_addresses_pk}',")
            sql = sql + str(f"'{str(sql_email_addresses).replace(chr(39),str(r'&#39')).replace(chr(39),str(r'&#39'))}')")+str(chr(10))
        else:
            sql_email_addresses=eml['email_addresses']
            for emailaddr_val in sql_email_addresses:
                sql = sql + str(f"insert into email_addresses(email,email_address) values('{email_addresses_pk}',")
                sql = sql + str(f"'{str(emailaddr_val).replace(chr(39),str(r'&#39'))}')")+str(chr(10)) 
        if str(eml['attachments']) is str("[]") or len(eml['attachments'])==0:
            sql_attachments = str(r"NULL")
            sql = sql + str(f"insert into attachments(email,attachment) values('{attachments_pk}',")
            sql = sql + str(f"'{str(sql_attachments).replace(chr(39),str(r'&#39')).replace(chr(39),str(r'&#39'))}')")+str(chr(10))
        else:
            sql_attachments=eml['attachments']
            for sql_val in sql_attachments:
                sql = sql + str(f"insert into attachments(email,attachment) values('{attachments_pk}',")
                sql = sql + str(f"'{str(sql_val).replace(chr(39),str(r'&#39'))}')")+str(chr(10))
        if str(eml['named_entities']) is str("[]") or len(eml['named_entities'])==0:
            sql_named_entities = str(r"NULL")
            sql = sql + str(f"insert into named_entities(email,type,entity) values('{named_entities_pk}',")
            sql = sql + str(f"'{str(sql_named_entities).replace(chr(39),str(r'&#39')).replace(chr(39),str(r'&#39'))}',")+str(chr(10))
            sql = sql + str(f"'{str(sql_named_entities).replace(chr(39),str(r'&#39')).replace(chr(39),str(r'&#39'))}')")+str(chr(10))
        else:
            sql_named_entities=eml['named_entities']
            for ner_val in  sql_named_entities:
                sql = sql + str(f"insert into named_entities(email,type,entity) values('{named_entities_pk}',")
                sql = sql + str(f"'{str(ner_val[0]).replace(chr(39),str(r'&#39'))}',")
                sql = sql + str(f"'{str(ner_val[1]).replace(chr(39),str(r'&#39'))}')")+str(chr(10))
        with open(f"/mnt/p/msg/eml_sql.sql","a") as fi:
            fi.write(str(unidecode(sql))+'\n')
        # cursor.execute(sql)
        # conn.commit()


def body_parse(msg_body:str):
    all_words = str("")
    phone_numbers = []
    msg_body_str = str(unidecode(msg_body)).replace('\r\n',' ').lower().replace('\n',' ').replace(r'%0d',' ').replace(r'%0a',' ').replace('<','').replace('>','')
    msg_body_str = str(msg_body_str).replace('\n','').replace('(','').replace(')','-').replace('https://','').replace('htt/mnt/p//','').replace('mailto:','')
    email_addr = np.unique(np.array([x for x in c.rm_wh(msg_body_str).split(' ') if str(x).find('@')!=-1 and str(x).find('.')!=-1 and str(x).find('@')<str(x).find('.')])).tolist()
    phone_numbers1 = np.unique(np.array(re.findall(r"([ ]{1}\d{3}[.+\D\W\s]{1}\d{3}[.+\D\W\s]{1}\d{4}[ ]{1})",str(''.join(str(x)+chr(32) for x in c.rm_wh(msg_body_str).split(' ')))))).tolist()
    phone_numbers2 = np.unique(np.array(re.findall(r"([ ]{1}\d{10}[ ]{1})",str(''.join(str(x)+chr(32) for x in c.rm_wh(msg_body_str).split(' ')))))).tolist()
    whitelist = set('abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ:@-._ ')
    ph_cheat = [phone_numbers.append(str(c.rm_wh(c.rm_sp(x))).replace(chr(32),''))for x in phone_numbers1
                ]+[phone_numbers.append(c.rm_wh(c.rm_sp(x)).replace(chr(32),''))for x in phone_numbers2]
    len(ph_cheat)
    msg_body_stripped = [''.join(str(x)+chr(32) for x in c.rm_wh(msg_body_str).split(' ') if len(x)>2)]
    msg_body_parse = [x for x in msg_body_stripped if len(x)>2]
    for p in msg_body_parse:
            all_words = str(all_words) + str(p) + chr(32)
    spacy_nlp = nlp(all_words)
    ner = [(n.text,n.start_char,n.end_char, n.label_) for n in spacy_nlp.ents]
    ner_list = []
    ner_list=[ [list(x)[3],list(x)[0]] for x in ner]
    text_tokens = word_tokenize(all_words)
    stops = stopwords.words('english')
    no_stop_words = [s for s in text_tokens if s.lower() not in stops and not len(s) < 2]
    all_uniques = np.unique(np.array(no_stop_words)).tolist()
    whitelist = set('abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ')
    msg_body_stripped = [''.join(l for l in str(x)+chr(32) if l in whitelist) for x in c.rm_wh(msg_body).split(' ')  if len(x)>2]
    msg_body_parse = [x for x in msg_body_stripped 
                      if len(x)>2
                      and str(x).find(r"http")==-1
                      and str(x).find(r"mailto")==-1
                      and str(x).find(r"www")==-1
                      and str(x).find(r"mailto")==-1
                      and str(x)[-3:]!=r"com"
                      ]
    msg_body_uniq = np.unique(np.array(msg_body_parse)).tolist()
    for p in msg_body_uniq:
            all_words = all_words + p + " "
    tt = word_tokenize(all_words)
    nsw = [s for s in tt if s.lower() not in stops and not len(s) < 2]
    unique_words = np.unique(np.array(nsw)).tolist()
    return all_uniques, unique_words, phone_numbers, email_addr, ner_list


def ret_addrs(f:str)->list[str]:
    msg = extract_msg.Message(f)
    msg_body = str(msg.body)
    msg_body_str = str(unidecode(msg_body)).replace('\r\n',' ').lower().replace('\n',' ').replace(r'%0d',' ').replace(r'%0a',' ').replace('<','').replace('>','')
    msg_body_str = str(msg_body_str).replace('\n','').replace('(','').replace(')','-').replace('https://','').replace('htt/mnt/p//','').replace('mailto:','')
    email_addr = np.unique(np.array([x for x in c.rm_wh(msg_body_str).split(' ') if str(x).find('@')!=-1 and str(x).find('.')!=-1 and str(x).find('@')<str(x).find('.')])).tolist()
    return email_addr


def msg_proc(f:str)-> None:
    f_id = str(os.path.basename(f)).replace(f[-(f[::-1].find('.'))-1:],'')
    msg = extract_msg.Message(f)
    msg_body = str(msg.body)
    all_uniques, unique_words, phone_numbers, email_addr, ner_list = body_parse(msg_body)
    msg_body = c.rm_wh(str(msg_body).replace(chr(34),'').replace(chr(39),'').replace('\r\n',' ').replace('\n',' ').replace(f'\\r\\n',' ').replace(f'\\n',' '))
    msg_body_bytes = bytes(str(f"{msg.body}"),encoding='utf-8')
    body_md5 = str(hashlib.md5(msg_body_bytes).hexdigest())
    if msg.date is not None:
        msg_date = dt.strptime(msg.date, "%a, %d %b %Y %H:%M:%S %z")
        msg_fdate = msg_date.strftime("%Y%m%d%H%M%S")
    elif msg.date is None:
        msg_fdate = str('None')
    msg_attachments = [a.displayName for a in msg.attachments]
    msg.attachments.
    c.emails = {
                'filename':f,
                'file_id':f_id,
                'date':msg_fdate,
                'msg_class':msg.classType,
                'body_md5':body_md5,
                'body':msg_body,
                'all_uniques':all_uniques,
                'unique_words':unique_words,
                'phone_numbers':phone_numbers,
                'email_addresses':email_addr,
                'sender':str(msg.sender),
                'to':str(msg.to),
                'message_id':str(msg.messageId),
                'header':str(msg.headerDict),
                'subject':str(msg.subject),
                'cc':str(msg.cc),
                'bcc':str(msg.bcc),
                'attachments':msg_attachments,
                'named_entities':ner_list}
    msg.close()
    return None

def proc_file()->str:
    c.file_path = str("")
    print("File Path:",end="")
    c.file_path = str(input()).replace(chr(34),'')
    print("\n")
    if os.path.isdir(c.file_path):
        if c.file_path[-1:] != "/":
            c.file_path = c.file_path+"/"
            return c.file_path
    if os.path.isfile(c.file_path):
        return c.file_path
    print("\n",c.file_path,"\n")


def ret_addrs(f:str)->list[str]:
    msg = extract_msg.Message(f)
    msg_body = str(msg.body)
    msg_body_str = str(unidecode(msg_body)).replace('\r\n',' ').lower().replace('\n',' ').replace(r'%0d',' ').replace(r'%0a',' ').replace('<','').replace('>','')
    msg_body_str = str(msg_body_str).replace('\n','').replace('(','').replace(')','-').replace('https://','').replace('htt/mnt/p//','').replace('mailto:','')
    email_addr = np.unique(np.array([x for x in c.rm_wh(msg_body_str).split(' ') if str(x).find('@')!=-1 and str(x).find('.')!=-1 and str(x).find('@')<str(x).find('.')])).tolist()
    return email_addr

if __name__ == "__main__":
    msg_email_addrs = []
    ffit_eml_addrs = []
    proc_file()
    if os.path.isdir(c.file_path):
        c.email_files = [c.file_path+f for f in os.listdir(c.file_path[:-1:]) if os.path.isfile(c.file_path+f) and f[-(f[::-1].find('.')):] in ['msg']]
        for msg_file in tqdm(c.email_files):
            msg_email_addrs = ret_addrs(msg_file)
            list(map(lambda x:ffit_eml_addrs.append(str(x)) if str(x).find('') !=-1 and str(x) not in ffit_eml_addrs else print("",end=""), [x for x in (msg_email_addrs)]))
    elif os.path.isfile(c.file_path):
        msg_email_addrs = ret_addrs(c.file_path)
        list(map(lambda x:ffit_eml_addrs.append(str(x)) if str(x).find('') !=-1 and str(x) not in ffit_eml_addrs else print("",end=""), [x for x in (msg_email_addrs)]))
    ffit_eml_addrs
    for eml_addr in ffit_eml_addrs:
        print(eml_addr)





