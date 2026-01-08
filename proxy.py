# cf_http_double_check.py
import requests
import concurrent.futures
import os
import cloudscraper
import threading

# Danh sách API HTTP proxy (VIP + Free)
APIS_HTTP = [
    # Proxyscrape
    "https://api.proxyscrape.com/v2/?request=getproxies&protocol=http&timeout=10000&country=all",
    # Proxy-list.download
    "https://www.proxy-list.download/api/v1/get?type=http",
    # OpenProxy
    "https://openproxy.space/list/http",
    # Proxy-list (raw)
    "https://raw.githubusercontent.com/TheSpeedX/PROXY-List/master/http.txt",
    "https://raw.githubusercontent.com/clarketm/proxy-list/master/proxy-list-raw.txt",
    "https://raw.githubusercontent.com/ShiftyTR/Proxy-List/master/http.txt",
    "https://raw.githubusercontent.com/jetkai/proxy-list/main/online-proxies/txt/proxies-http.txt",
    # Geonode (API JSON, nhưng chỉ lấy type HTTP)
    "https://proxylist.geonode.com/api/proxy-list?limit=500&page=1&sort_by=lastChecked&sort_type=desc&protocols=http",
]

OUT_FILE = "http.txt"
lock = threading.Lock()

# Biến toàn cục để đếm số proxy đã check
checked_count = 0
checked_lock = threading.Lock()

# B1: Check proxy sống (httpbin.org)
def check_alive(proxy):
    global checked_count
    test_url = "https://httpbin.org/ip"
    proxies = {"http": f"http://{proxy}", "https": f"http://{proxy}"}
    try:
        r = requests.get(test_url, proxies=proxies, timeout=1)
        if r.status_code == 200:
            with checked_lock:
                checked_count += 1
                print(f"🔍 Đã check {checked_count} proxy sống", end="\r")
            return proxy
    except:
        with checked_lock:
            checked_count += 1
            print(f"🔍 Đã check {checked_count} proxy sống", end="\r")
        return None
    return None

# B2: Check qua Cloudflare (cdn-cgi/trace) + lưu ngay
def check_cloudflare(proxy):
    global checked_count
    test_url = "https://www.cloudflare.com/cdn-cgi/trace"
    proxies = {"http": f"http://{proxy}", "https": f"http://{proxy}"}
    try:
        scraper = cloudscraper.create_scraper()
        r = scraper.get(test_url, proxies=proxies, timeout=5)
        if r.status_code == 200:
            with lock:
                with open(OUT_FILE, "a") as f:
                    f.write(proxy + "\n")
                print(f"✅ Lưu proxy: {proxy}")
            with checked_lock:
                checked_count += 1
                print(f"🌐 Đã check {checked_count} proxy Cloudflare", end="\r")
            return proxy
    except:
        with checked_lock:
            checked_count += 1
            print(f"🌐 Đã check {checked_count} proxy Cloudflare", end="\r")
        return None
    return None

# Lấy proxy từ API
def fetch_api(url):
    proxies = []
    try:
        if "geonode.com" in url:
            r = requests.get(url, timeout=10).json()
            for p in r.get("data", []):
                ip, port = p.get("ip"), p.get("port")
                if ip and port:
                    proxies.append(f"{ip}:{port}")
        else:
            r = requests.get(url, timeout=10)
            for line in r.text.splitlines():
                if ":" in line:
                    proxies.append(line.strip())
    except:
        pass
    return proxies

def main():
    global checked_count
    
    # Xoá file cũ
    if os.path.exists(OUT_FILE):
        os.remove(OUT_FILE)
        print(f"🗑️ Đã xoá file cũ: {OUT_FILE}")

    # tải proxy
    all_proxies = []
    print("🌐 Đang đào HTTP proxy từ API VIP...")
    for url in APIS_HTTP:
        all_proxies.extend(fetch_api(url))

    all_proxies = list(set(all_proxies))
    print(f"🔍 Tổng proxy HTTP lấy được: {len(all_proxies)}")

    # B1: check proxy sống
    print("⚡ Đang check proxy sống...")
    checked_count = 0  # Reset counter
    with concurrent.futures.ThreadPoolExecutor(max_workers=100) as executor:
        alive_results = list(executor.map(check_alive, all_proxies))
    print()  # Xuống dòng sau khi hoàn thành
    alive = [p for p in alive_results if p]
    print(f"✅ Proxy sống: {len(alive)}/{len(all_proxies)}")

    # B2: check Cloudflare + lưu ngay
    print("🌐 Đang check proxy qua Cloudflare...")
    checked_count = 0  # Reset counter
    with concurrent.futures.ThreadPoolExecutor(max_workers=100) as executor:
        list(executor.map(check_cloudflare, alive))
    print()  # Xuống dòng sau khi hoàn thành

    # báo cáo cuối
    with open(OUT_FILE, "r") as f:
        saved = f.read().splitlines()
    print(f"\n🎯 Hoàn tất: {len(saved)} proxy vượt Cloudflare đã lưu vào {OUT_FILE}")

if __name__ == "__main__":
    main()