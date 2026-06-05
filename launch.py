import os, threading, secrets, webview
os.environ.setdefault('INTSHUBA_DATA_DIR', os.path.expanduser('~/.intshuba'))
os.environ.setdefault('SECRET_KEY', secrets.token_hex(32))
os.makedirs(os.environ['INTSHUBA_DATA_DIR'], exist_ok=True)
def run():
    import intshuba; intshuba.app.run(host='127.0.0.1',port=5100,debug=False,use_reloader=False)
threading.Thread(target=run,daemon=True).start()
__import__('time').sleep(2)
webview.create_window('Intshuba — Inkazimulo Digital','http://127.0.0.1:5100',width=1280,height=800)
webview.start()
