#include <lean/lean.h>
#include <libxml/parser.h>
#include <libxml/tree.h>
#include <archive.h>
#include <archive_entry.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#define LIMIT (16*1024*1024)
static lean_object *bad(const char *s) { return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(s))); }
lean_object *calc_zip_text(lean_object *path, lean_object *entry) {
    struct archive *a=archive_read_new(); struct archive_entry *e;
    archive_read_support_format_zip(a); archive_read_support_filter_none(a);
    if (archive_read_open_filename(a,lean_string_cstr(path),65536)!=ARCHIVE_OK) {archive_read_free(a);return bad("Cannot read ODS ZIP archive.");}
    char *data=NULL; size_t used=0; int found=0, ok=1;
    while (archive_read_next_header(a,&e)==ARCHIVE_OK) {
        if (strcmp(archive_entry_pathname(e),lean_string_cstr(entry))) {archive_read_data_skip(a);continue;}
        if (found++ || archive_entry_size(e)>LIMIT || archive_entry_is_encrypted(e)) {ok=0;break;}
        data=malloc(LIMIT+1); if (!data) {ok=0;break;}
        for (;;) {la_ssize_t n=archive_read_data(a,data+used,LIMIT-used); if(n<0){ok=0;break;} if(!n)break;used+=n;if(used>=LIMIT){ok=0;break;}}
        if(!ok)break;
    }
    archive_read_free(a);
    if(!ok || !found || memchr(data,0,used)) {free(data);return bad("Missing, duplicate, encrypted, oversized, or invalid ODS XML entry.");}
    data[used]=0;lean_object *result=lean_io_result_mk_ok(lean_mk_string(data));free(data);return result;
}
typedef struct {char *s;size_t n,cap;int ok,nodes;} Buf;
static void add(Buf *b,const char *s) {size_t n=strlen(s);if(!b->ok)return;if(b->n+n>LIMIT*4){b->ok=0;return;}if(b->n+n+1>b->cap){size_t c=(b->n+n+1)*2;void *p=realloc(b->s,c);if(!p){b->ok=0;return;}b->s=p;b->cap=c;}memcpy(b->s+b->n,s,n+1);b->n+=n;}
static void quote(Buf *b,const char *s) {add(b,"\"");for(const unsigned char *p=(const unsigned char*)s;*p;p++){char v[8];if(*p=='"'||*p=='\\'){v[0]='\\';v[1]=*p;v[2]=0;}else if(*p<32){snprintf(v,sizeof(v),"\\u%04x",*p);}else{v[0]=*p;v[1]=0;}add(b,v);}add(b,"\"");}
static const char *prefix(const xmlChar *uri) {
 if(!uri)return "";
 const char *u=(const char*)uri;
 if(!strcmp(u,"urn:oasis:names:tc:opendocument:xmlns:office:1.0"))return "office";
 if(!strcmp(u,"urn:oasis:names:tc:opendocument:xmlns:table:1.0"))return "table";
 if(!strcmp(u,"urn:oasis:names:tc:opendocument:xmlns:text:1.0"))return "text";
 if(!strcmp(u,"urn:oasis:names:tc:opendocument:xmlns:drawing:1.0"))return "draw";
 if(!strcmp(u,"urn:oasis:names:tc:opendocument:xmlns:style:1.0"))return "style";
 if(!strcmp(u,"urn:oasis:names:tc:opendocument:xmlns:datastyle:1.0"))return "number";
 if(!strcmp(u,"urn:oasis:names:tc:opendocument:xmlns:xsl-fo-compatible:1.0"))return "fo";
 return "other";
}
static void name(Buf *b,const xmlChar *local,xmlNs *ns) {char s[512];snprintf(s,sizeof(s),"%s:%s",prefix(ns?ns->href:NULL),(const char*)local);quote(b,s);}
static void plain(Buf *b,xmlNode *n,int depth) {
 if(depth>64){b->ok=0;return;}
 for(xmlNode *c=n->children;c;c=c->next) {
  if(c->type==XML_TEXT_NODE||c->type==XML_CDATA_SECTION_NODE) {add(b,(const char*)c->content);continue;}
  if(c->type!=XML_ELEMENT_NODE)continue;
  const char *ns=prefix(c->ns?c->ns->href:NULL);
  if(!strcmp(ns,"text")&&!strcmp((char*)c->name,"s")) {
   xmlChar *count=xmlGetNsProp(c,(xmlChar*)"c",(xmlChar*)"urn:oasis:names:tc:opendocument:xmlns:text:1.0");
   long spaces=count?strtol((char*)count,NULL,10):1;xmlFree(count);
   if(spaces<1||spaces>4096){b->ok=0;return;}while(spaces--)add(b," ");
  } else if(!strcmp(ns,"text")&&!strcmp((char*)c->name,"tab"))add(b,"\t");
  else if(!strcmp(ns,"text")&&!strcmp((char*)c->name,"line-break"))add(b,"\n");
  else plain(b,c,depth+1);
 }
}
static void node(Buf *b,xmlNode *n,int depth) {
 if(depth>64||++b->nodes>100000){b->ok=0;return;}
 add(b,"{\"tag\":");name(b,n->name,n->ns);add(b,",\"attrs\":[");int first=1;
 for(xmlAttr *a=n->properties;a;a=a->next){if(!first)add(b,",");first=0;add(b,"[");name(b,a->name,a->ns);add(b,",");xmlChar *v=xmlNodeListGetString(n->doc,a->children,1);quote(b,v?(char*)v:"");xmlFree(v);add(b,"]");}
 add(b,"],\"text\":");Buf text={.ok=1};plain(&text,n,0);if(!text.ok)b->ok=0;quote(b,text.s?text.s:"");free(text.s);add(b,",\"children\":[");first=1;
 for(xmlNode *c=n->children;c;c=c->next)if(c->type==XML_ELEMENT_NODE){if(!first)add(b,",");first=0;node(b,c,depth+1);}
 add(b,"]}");
}
lean_object *calc_xml_tree(lean_object *text) {
 const char *s=lean_string_cstr(text);size_t size=strlen(s);
 if(size>LIMIT||strstr(s,"<!DOCTYPE")||strstr(s,"<!ENTITY"))return bad("DTD/entities or oversized XML are not supported.");
 xmlDoc *doc=xmlReadMemory(s,(int)size,"content.xml",NULL,XML_PARSE_NONET|XML_PARSE_NOERROR|XML_PARSE_NOWARNING);
 if(!doc)return bad("Invalid ODS XML.");
 Buf b={.ok=1};xmlNode *root=xmlDocGetRootElement(doc);if(root)node(&b,root,0);else b.ok=0;xmlFreeDoc(doc);
 lean_object *r=b.ok?lean_io_result_mk_ok(lean_mk_string(b.s)):bad("ODS XML exceeds structural limits.");free(b.s);return r;
}
