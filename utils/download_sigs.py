import requests
from requests.adapters import HTTPAdapter

JSON_MEDIA_TYPE = 'application/json'
MAX_RETRIES = 3




session = requests.Session()
session.mount("www.4byte.directory", HTTPAdapter(max_retries=MAX_RETRIES))

result_list = []
headers = {'Content-Type': JSON_MEDIA_TYPE}

for page in range(1,60):
    print("retrieving page " + str(page))

    url = 'https://www.4byte.directory/api/v1/signatures/?format=json&page=' + str(page)

    try:
        r = session.get(url, headers=headers)
        response = r.json()
    except ValueError:
        raise BadJsonError(r.text)

    result_list += response['results']

print(result_list)
